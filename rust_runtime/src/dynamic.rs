use crate::{
    conv::{
        len::{Estimable, FixedLength},
        Decode, Encode, EncodeLength,
    },
    int::u30,
    parse::{ParseResult, Parser},
};
use std::{
    convert::TryFrom,
    fmt::{Debug, Display},
    marker::PhantomData,
    ops::Deref,
};

/// `Wrapper<T>`: Trait used to mark a shallow wrapper around a payload type,
/// with means to infallibly coerce between the raw and wrapped form.
pub trait Wrapper<T> {
    /// Wraps a value of type `T` into a `Self` object.
    fn wrap(val: T) -> Self;

    /// Unwraps a value of type `T` from a `Self` object, consuming it.
    fn unwrap(self) -> T;
}

/// `Dynamic<S, T>`: Schema-level construct for explicit dynamic length of variable-length types
///
/// Consists of a payload of type `T`, preceded by a length-prefix of the
/// specified unsigned integral type `S`. The value of the `S`-typed prefix
/// indicates the exact number of bytes in the payload of type `T`.
///
/// The generic parameter `S` must implement the trait `LenPref`, which is
/// marked unsafe as it is a closed class containing only [`u8`], [`u16`],
/// and [`u30`](crate::int::u30).
///
/// # Implementation Notes
///
/// The [`std::fmt::Debug`] implementation for this type is optimized for
/// readability rather than specificity, and only indicates the dynamic
/// length of the payload, not the byte-width of the prefix.
///
/// As this type is a shallow wrapper around a significant value `T`,
/// the [`std::fmt::Display`] implementation merely calls the implementation
/// via `<T as Display>`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dynamic<S: LenPref, T> {
    contents: T,
    _phantom: PhantomData<S>,
}

impl<S: LenPref, T> Wrapper<T> for Dynamic<S, T> {
    /// Wraps a value of type `T` into a `Dynamic<S, T>` object.
    ///
    /// This is mostly useful when attempting to fit a variable-length value
    /// of type `T` into a codec type in which it appears in the form `Dynamic<S, T>`
    /// for some `S`.
    ///
    /// Note that the value to be wrapped is not length-checked
    /// to ensure it can be serialized in no fewer than `M` bytes,
    /// where `M` is the maximum value in the range of `S`;
    /// this check is only done during the encoding step, and
    /// will result in a panic if this condition is violated.
    fn wrap(contents: T) -> Self {
        Self {
            contents,
            _phantom: PhantomData,
        }
    }

    /// Destructor for `Dynamic<S, T>` that returns the contained
    /// payload of type `T`.
    ///
    /// This is mostly useful when attempting to extract the payload
    /// values from a codec type that holds `Dynamic<S, T>`, after
    /// the codec type has been decoded.
    fn unwrap(self) -> T {
        self.contents
    }
}

impl<S: LenPref, T: Estimable> Estimable for Dynamic<S, T> {
    const KNOWN: Option<usize> = {
        const fn f(x: Option<usize>, y: Option<usize>) -> Option<usize> {
            match (x, y) {
                (Some(m), Some(n)) => Some(m + n),
                _ => None,
            }
        }
        f(S::KNOWN, T::KNOWN)
    };

    fn unknown(&self) -> usize {
        <S as FixedLength>::LEN + self.contents.estimate()
    }
}

impl<S: LenPref, T: Debug + Estimable> Debug for Dynamic<S, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}{} bytes|{:?}]",
            self.contents.estimate(),
            S::suffix(),
            self.contents
        )
    }
}

impl<S: LenPref, T: Display> Display for Dynamic<S, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.contents, f)
    }
}

impl<S: LenPref, T> Deref for Dynamic<S, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.contents
    }
}

impl<S: LenPref, T> From<T> for Dynamic<S, T> {
    fn from(val: T) -> Self {
        Self {
            contents: val,
            _phantom: std::marker::PhantomData,
        }
    }
}

/// `LenPref`: marker trait for the closed set of types suitable for use
/// as the dynamic length prefix type-parameter `S` of [`Dynamic<S,T>`](Dynamic).
///
/// Specifically, the only valid implementors are [`u8`], [`u16`], and [`u30`](crate::int::u30).
///
/// As this is a closed trait, it is made public for use as a valid trait-bound on the public type
/// `Dynamic`, but is marked `unsafe` to prevent casual implementation on types other than these three.
///
/// In addition to being a marker, this trait also presents the necessary bounds shared by the three
/// valid length-prefix types: infallible coercion to and fallible conversion from `usize`, `Copy`,
/// [`Encode`](crate::conv::Encode) (via [`EncodeLength`](crate::conv::EncodeLength)), [`Decode`](crate::conv::Decode),
/// and [`FixedLength`](crate::conv::len::FixedLength).
pub unsafe trait LenPref
where
    Self: Into<usize> + TryFrom<usize> + Copy + EncodeLength + Decode + FixedLength,
{
    fn suffix() -> &'static str {
        std::any::type_name::<Self>()
    }
}

unsafe impl LenPref for u8 {}
unsafe impl LenPref for u16 {}
unsafe impl LenPref for u30 {
    fn suffix() -> &'static str {
        "u30"
    }
}

impl<S: LenPref, T: EncodeLength> Encode for Dynamic<S, T> {
    fn write_to<U: crate::conv::target::Target>(&self, buf: &mut U) -> usize {
        let l: usize = self.contents.enc_len();
        match S::try_from(l) {
            Ok(lp) => {
                buf.anticipate(l + <S as EncodeLength>::enc_len(&lp));
                crate::write_all_to!(lp, self.contents => buf)
            }
            Err(_) => {
                panic!(
                    "Dynamic<{}, _>: Length prefix {} exceeds bounds of associated type",
                    std::any::type_name::<S>(),
                    l
                );
            }
        }
    }
}

impl<S: LenPref, T: Decode> Decode for Dynamic<S, T> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let buflen = S::parse(p)?;
        p.set_fit(buflen.into())?;
        let contents = T::parse(p)?;
        p.enforce_target()?;
        Ok(Dynamic {
            contents,
            _phantom: PhantomData,
        })
    }
}

/// `VPadded<T, N>`: Wrapper type around `T` that virtually "pads" it with `N` bytes for the purposes
/// of determining when a variable-length field (or tuple positional argument) terminates.
///
/// A value of type `VPadded<T, N>` is semantically equivalent to a value of type `T` for almost
/// any purpose, except for the purposes of parsing. In particular, when a value of type
/// `VPadded<T, N>` has been fully parsed (and does not panic or otherwise fail), there will be
/// exactly `N` unparsed bytes left in the current surrounding parse-context, which have been reserved
/// for a fixed-length tail of remaining fields or arguments in a record or tuple-like container.
///
/// In terms of syntax, `VPadded<T, N>` is similar to [`Padded<T, N>`](crate::schema::Padded),
/// though the operational semantics of the two with respect to encoding and decoding are entirely
/// distinct.
///
/// It is technically valid to have a value of type `VPadded<_, 0>` just as it is valid to have a value
/// of type `Padded<_, 0>`, though neither one is expected to appear in codecs as they are fundamentally
/// indistinguishable from the payload type, and each other, for the purposes of encoding and decoding.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct VPadded<T, const N: usize>(T);

impl<T: Debug, const N: usize> Debug for VPadded<T, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as Debug>::fmt(&self.0, f)
    }
}

impl<T, const N: usize> Wrapper<T> for VPadded<T, N> {
    /// Wraps a value of type `T` into a `VPadded<T, N>` object.
    ///
    /// This is mostly useful when attempting to fit raw values
    /// into a codec type that expects `VPadded<T, N>`, to be
    /// encoded.
    fn wrap(val: T) -> Self {
        Self(val)
    }

    /// Destructor for `VPadded<T, N>` that returns the contained
    /// payload of type `T`.
    ///
    /// This is mostly useful when attempting to extract the payload
    /// values from a codec type that holds `VPadded<T, N>`, after
    /// the codec type has been decoded.
    fn unwrap(self) -> T {
        self.0
    }
}

impl<T, const N: usize> Deref for VPadded<T, N> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, const N: usize> From<T> for VPadded<T, N> {
    fn from(val: T) -> Self {
        Self(val)
    }
}

impl<T: Encode, const N: usize> Encode for VPadded<T, N> {
    fn write_to<U: crate::Target>(&self, buf: &mut U) -> usize {
        self.0.write_to(buf) + crate::resolve_zero(buf)
    }
}

impl<T: Decode, const N: usize> Decode for VPadded<T, N> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let _rem = p.remainder();
        debug_assert!(
            _rem >= N,
            "Cannot parse VPadded<{}, {}> with {} (< {}) bytes remaining",
            std::any::type_name::<T>(),
            N,
            _rem,
            N
        );
        p.set_fit(_rem - N)?;
        let ret = T::parse(p)?;
        p.enforce_target()?;
        Ok(Self(ret))
    }
}

impl<T: Estimable, const N: usize> Estimable for VPadded<T, N> {
    const KNOWN: Option<usize> = T::KNOWN;

    fn unknown(&self) -> usize {
        self.0.unknown()
    }
}
