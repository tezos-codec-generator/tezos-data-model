use crate::conv::len::FixedLength;
use crate::conv::{Decode, Encode};
use crate::error::BoundsError;
use crate::parse::ParseResult;
use crate::Parser;
use num_integer::Integer;
use std::convert::{TryFrom, TryInto};
use std::fmt::Debug;

mod private {
    pub trait Sealed {}

    impl Sealed for u8 {}
    impl Sealed for i8 {}
    impl Sealed for i16 {}
    impl Sealed for u16 {}
    impl Sealed for u32 {}
    impl Sealed for i32 {}
}
/// Marker for suitability as 'backer' of a `RangedInt`
///
/// In the `data-encoding` OCaml library, range-bound integral values must
/// be representable in 4 bytes or fewer. This means that the only legal
/// backers for the `RangedInt` type are the following:
///   * [`u8`] or [`i8`]
///   * [`u16`] or [`i16`]
///   * [`u32`] or [`i32`]
///
/// This is a sealed trait that cannot be implemented downstream.
pub trait Integral
where
    Self: Copy + std::hash::Hash + std::fmt::Display,
    Self: Integer + Into<i64> + TryFrom<i64>,
    Self: Eq + PartialEq + Ord + PartialOrd,
    Self: private::Sealed,
{
}

impl Integral for u8 {}
impl Integral for i8 {}
impl Integral for u16 {}
impl Integral for i16 {}
impl Integral for u32 {}
impl Integral for i32 {}

/// Minimum value representable using OCaml 31-bit integers
///
/// ```
/// # use ::rust_runtime::int::MIN_OCAML_NATIVE_INT;
/// assert_eq!(MIN_OCAML_NATIVE_INT, -(1i32 << 30));
/// assert_eq!(MIN_OCAML_NATIVE_INT, i32::MIN / 2);
/// ```
///
pub const MIN_OCAML_NATIVE_INT: i32 = -0x4000_0000;

/// Maximum value representable using OCaml 31-bit integers
///
/// ```
/// # use ::rust_runtime::int::MAX_OCAML_NATIVE_INT;
/// assert_eq!(MAX_OCAML_NATIVE_INT, (1i32 << 30) - 1);
/// assert_eq!(MAX_OCAML_NATIVE_INT, i32::MAX / 2);
/// ```
pub const MAX_OCAML_NATIVE_INT: i32 = 0x3fff_ffff;

/// Maximum value representable using OCaml 30-bit unsigned integers
///
/// ```
/// # use ::rust_runtime::int::MAX_OCAML_NATIVE_UINT;
/// assert_eq!(MAX_OCAML_NATIVE_UINT, (1u32 << 30) - 1);
/// assert_eq!(MAX_OCAML_NATIVE_UINT, (u32::MAX >> 2));
/// ```
pub const MAX_OCAML_NATIVE_UINT: u32 = 0x3fff_ffff;

/// Integral value that is implicitly confined to a constant range `[MIN,MAX]`
///
/// # Representation
///
/// The details of the intended representation vary based on the
/// range `[MIN, MAX]` in question, or, more precisely,
/// on the sign of `MIN` and the difference `MAX - MIN`.
///
/// ## `MIN < 0`
///
/// When `MIN < 0`, `I` will always be a signed integer primitive
/// (`i8`, `i16`, or `i32`), and the actual value stored opaquely
/// within the `RangedInt` struct is precisely the integer value
/// being represented.
///
/// ## `MIN == 0`
///
/// When `MIN == 0`, `I` will always be an unsigned integer primitive
/// (`u8`, `u16`, or `u32`), and the actual value stored opaquely
/// within the `RangedInt` struct is precisely the integer value
/// being represented.
///
/// ## `MIN > 0`
///
/// When `MIN > 0`, `I` will always be an unsigned integer primitive,
/// (`u8`, `u16`, or `u32`), and the actual value stored opaquely
/// within the `RangedInt` struct is the **positive offset** measured
/// from `MIN` of the value being represented.
///
/// This distinction is critical in cases where either `MIN` or `MAX`
/// are not representable using direct values of `I`, but their difference
/// can be, such as `RangedInt::<u8, 1023, 1024>`.
///
/// # Bound Limits
///
/// The generic const bounds must satisfy the following invariant in order
/// to be a sound type:
///
/// [`MIN_OCAML_NATIVE_INT`]` <= MIN <= MAX <= `[`MAX_OCAML_NATIVE_INT`]
///
/// If this condition is not met, the type itself is unsound, and
/// attempting to use such a type may result in a runtime panic.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd, Debug, Hash)]
#[repr(transparent)]
pub struct RangedInt<I: Integral, const MIN: i32, const MAX: i32>(I);

#[allow(non_camel_case_types)]
#[allow(dead_code)]
/// Type alias for the range of `Uint30` codecs, from `0` to `2^30 - 1`
pub type u30 = RangedInt<u32, 0, MAX_OCAML_NATIVE_INT>;

#[allow(non_camel_case_types)]
#[allow(dead_code)]
/// Type alias for the range of `Int31` codecs, from `-2^30` to `2^30 - 1`
pub type i31 = RangedInt<i32, MIN_OCAML_NATIVE_INT, MAX_OCAML_NATIVE_INT>;

impl<I: Integral, const MIN: i32, const MAX: i32> RangedInt<I, MIN, MAX> {
    /// Associated constant used for sanity-checking of the type-level generics
    /// `MIN` and `MAX`.
    ///
    /// `true` if and only if the selected `MIN` and `MAX` values represent
    /// a sound type.
    #[cfg(feature = "invalid_range_checking")]
    const SANITY: bool = MIN >= MIN_OCAML_NATIVE_INT && MAX <= MAX_OCAML_NATIVE_INT && MIN <= MAX;

    /// Converts a value `x` of the backer type `I` to a numerically equivalent value
    /// of type `RangedInt<I, MIN, MAX>`
    ///
    /// This function does not check that the provided value is in range, nor that the range
    /// itself is sound.
    ///
    /// # Safety
    ///
    /// This function does not panic, but it can be used to produce incoherent values or
    /// values of theoretically unpopulated types, and so using any value returned by this
    /// unsafe function may cause undefined behavior down the line.
    #[must_use]
    #[inline]
    pub unsafe fn from_value_unchecked(x: I) -> Self {
        // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
        Self(x)
    }

    /// Converts a value `x` of the backer type `I` to a numerically equivalent value
    /// of type `RangedInt<I, MIN, MAX>`, checking that the range `[MIN, MAX]` is
    /// coherent and that `x` falls into that range.
    ///
    /// # Panics
    ///
    /// If either of the checked conditions are violated, this function will panic.
    #[must_use]
    #[inline]
    pub fn from_value(x: I) -> Self {
        // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
        Self::try_from_value(x).expect("RangedInt::from_value encountered Err")
    }

    /// Attempt to convert a value `x` of the backer type `I` to a numerically equivalent
    /// value of type `RangedInt<I, MIN, MAX>`, checking that the range `[MIN, MAX]` is
    /// coherent and that `x` falls into that range.
    ///
    /// Returns `Ok` if the checks are satisfied, or `Err(e)` otherwise, where
    /// `e` is an indication of what required condition failed to hold for the
    /// attempted conversion.
    ///
    /// # Panics
    ///
    /// This function will never panic under normal compilations.
    ///
    /// If the `invalid-range-checking` feature is turned on, however, this
    /// function will panic if `[MIN, MAX]` is not a valid sub-range of
    /// `[`[`MIN_OCAML_NATIVE_INT`]`, `[`MAX_OCAML_NATIVE_INT`]`]`
    #[inline]
    pub fn try_from_value(x: I) -> Result<Self, crate::error::BoundsError<i64>> {
        // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
        #[cfg(feature = "invalid_range_checking")]
        assert!(
            Self::SANITY,
            "type-level bounds on RangedInt<{},{}> are invalid",
            MIN,
            MAX
        );

        Ok(Self(BoundsError::<i64>::restrict(x, MIN, MAX)?))
    }

    /// Destruct and return the numeric value of a `RangedInt<I, MIN, MAX>`
    /// without checking that it is in-range, or that the invariant `MIN <= MAX`
    /// holds.
    ///
    /// No checks are performed, and so values returned from calls to this destructor
    /// are not guaranteed to be in the implicit range `[MIN, MAX]`.
    ///
    /// # Safety
    ///
    /// This destructor is a dual to the constructor [`from_value_unchecked`],
    /// which is the only method that allows for the construction of numeric
    /// values outside of the range `[MIN, MAX]`. In turn, this destructor
    /// is the only one that is guaranteed not to panic or produce undefined
    /// behavior when applied to such out-of-bounds values.
    #[inline]
    pub unsafe fn to_value_unchecked(self) -> I {
        // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
        self.0
    }

    /// Extract the numeric value of a `RangedInt<I, MIN, MAX>`, checking that
    /// the value is in range, and that the range itself is coherent.
    ///
    /// # Panics
    ///
    ///
    pub fn to_value(self) -> I {
        // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
        #[cfg(feature = "invalid_range_checking")]
        assert!(
            Self::SANITY,
            "type-level bounds on RangedInt<{},{}> are invalid",
            MIN,
            MAX
        );

        match crate::error::BoundsError::<i64>::restrict(self.0, MIN, MAX) {
            Ok(x) => x,
            Err(err) => panic!("RangedInt::to_value unable to destruct: {}", err),
        }
    }
}

impl<I: Integral, const MIN: i32, const MAX: i32> AsRef<I> for RangedInt<I, MIN, MAX> {
    // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
    fn as_ref(&self) -> &I {
        &self.0
    }
}

pub mod ranged_int_impls {
    use super::*;

    macro_rules! impl_default_clamped {
        ( $t:ty ) => {
            impl<const MIN: i32, const MAX: i32> Default for RangedInt<$t, MIN, MAX> {
                /// Returns the value in the range [MIN..MAX] that is closest to the
                /// value of `Default::default()` for the backing type.
                fn default() -> Self {
                    // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
                    Self((<$t>::default() as i32).clamp(MIN, MAX) as $t)
                }
            }
        };
    }

    impl_default_clamped!(u8);
    impl_default_clamped!(i8);
    impl_default_clamped!(u16);
    impl_default_clamped!(i16);
    impl_default_clamped!(u32);
    impl_default_clamped!(i32);

    macro_rules! minval_maxval {
        ( $t:ty ) => {
            impl<const MIN_I32: i32, const MAX_I32: i32> RangedInt<$t, MIN_I32, MAX_I32> {
                // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
                pub const MIN: $t = MIN_I32 as $t;

                // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
                pub const MAX: $t = MAX_I32 as $t;


                /// Returns the minimum legal value of `Self`
                #[inline]
                pub const fn min_val() -> Self {
                    // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
                    Self(Self::MIN)
                }

                /// Returns the maximum legal value of `Self`
                #[inline]
                pub const fn max_val() -> Self {
                    // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
                    Self(Self::MAX)
                }
            }
        };
    }

    minval_maxval!(u8);
    minval_maxval!(i8);
    minval_maxval!(u16);
    minval_maxval!(i16);
    minval_maxval!(u32);
    minval_maxval!(i32);

    macro_rules! impl_from_ranged_int {
    ( $backer:ty => $( $dest:ty ),+ ) => {
        $(
            impl<const MIN: i32, const MAX: i32> From<RangedInt<$backer, MIN, MAX>> for $dest {
                // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
                fn from(val: RangedInt<$backer, MIN, MAX>) -> Self {
                    val.0 as $dest
                }
            }
        )+
        };
    }

    macro_rules! impl_try_from_ranged_int {
    ( $backer:ty => $( $dest:ty ),+ ) => {
        $(
            impl<const MIN: i32, const MAX: i32> TryFrom<RangedInt<$backer, MIN, MAX>> for $dest {
                type Error = <$backer as TryInto<$dest>>::Error;

                fn try_from(val: RangedInt<$backer, MIN, MAX>) -> Result<Self, Self::Error> {
                    // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
                    val.0.try_into()
                }
            }
        )+
        };
    }

    macro_rules! impl_try_into_ranged_int {
        (@for_types $( $src:ty ),+ => $backer:ty ) => {
            $(
            impl<const MIN: i32, const MAX: i32> TryFrom<$src> for RangedInt<$backer, MIN, MAX> {
                type Error = BoundsError<i128>;

                // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
                fn try_from(val: $src) -> Result<Self, Self::Error> {
                    match BoundsError::restrict(val, MIN, MAX) {
                        Ok(x) => unsafe { Ok(Self::from_value_unchecked(x as $backer)) }
                        Err(e) => Err(e)
                    }
                }
            }
            )+
        };
        ( $( $backer:ty ),+ ) => {
            $(
            impl_try_into_ranged_int!(@for_types u8, i8, u16, i16, u32, i32, u64, i64, usize, isize => $backer );
            )+
        }
    }

    impl_from_ranged_int!(u8 => u8, u16, i16, u32, i32, u64, i64, usize, isize);
    impl_from_ranged_int!(i8 => i8, i16, i32, i64, isize);
    impl_from_ranged_int!(i16 => i16, i32, i64, isize);
    impl_from_ranged_int!(u16 => u32, i32, u64, i64, usize, isize);
    impl_from_ranged_int!(i32 => i32, i64, isize);
    impl_from_ranged_int!(u32 => u32, i32, u64, i64, usize, isize);

    impl_try_from_ranged_int!(u8 => i8);
    impl_try_from_ranged_int!(u16 => i8, u8, i16);
    impl_try_from_ranged_int!(u32 => i8, u8, i16, u16);

    impl_try_from_ranged_int!(i8 => u8, u16, u32, u64, usize);
    impl_try_from_ranged_int!(i16 => i8, u8, u16, u32, u64, usize);
    impl_try_from_ranged_int!(i32 => i8, u8, i16, u16, u32, u64, usize);

    impl_try_into_ranged_int!(u8, i8, u16, i16, u32, i32);

    macro_rules! impl_numeric_fmt {
        ( $( $trait:ident ),+ ) => {
            $( impl<I, const MIN: i32, const MAX: i32> std::fmt::$trait for RangedInt<I, MIN, MAX>
            where
                I: Integral + std::fmt::$trait,
            {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    // FIXME: fix bug when MIN > 0 (and edit documentation appropriately)
                    <I as std::fmt::$trait>::fmt(self.as_ref(), f)
                }
            }
            )+
        };
    }

    impl_numeric_fmt!(Binary, Octal, LowerHex, UpperHex);

    impl<I, const MIN: i32, const MAX: i32> Encode for RangedInt<I, MIN, MAX>
    where
        I: Integral + Encode,
        <I as TryFrom<i64>>::Error: std::fmt::Debug,
    {
        fn write_to<U: crate::conv::target::Target>(&self, buf: &mut U) -> usize {
            let enc_val = if MIN > 0 {
                let val: i64 = self.to_value().into();
                let min: i64 = MIN.into();
                (val - min).try_into().unwrap()
            } else {
                self.to_value()
            };
            enc_val.write_to(buf) + buf.resolve_zero()
        }
    }

    impl<I, const MIN: i32, const MAX: i32> FixedLength for RangedInt<I, MIN, MAX>
    where
        I: Integral + FixedLength,
    {
        const LEN: usize = I::LEN;
    }

    impl<I, const MIN: i32, const MAX: i32> Decode for RangedInt<I, MIN, MAX>
    where
        I: Integral + Decode,
        <I as TryFrom<i64>>::Error: std::fmt::Debug,
    {
        fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
            let raw = I::parse(p)?;
            if MIN > 0 {
                let adjusted: i64 = <I as Into<i64>>::into(raw) + i64::from(MIN);
                match BoundsError::<i64>::restrict(adjusted, MIN, MAX) {
                    Ok(val) => match val.try_into() {
                        Ok(x) => Ok(unsafe { Self::from_value_unchecked(x) }),
                        Err(_) => unreachable!(), /* MIN <= val <= MAX should guarantee val is in its representational range */
                    },
                    Err(oor) => Err(oor.into()),
                }
            } else {
                match BoundsError::<i64>::restrict(raw, MIN, MAX) {
                    Ok(val) => Ok(unsafe { Self::from_value_unchecked(val) }),
                    Err(oor) => Err(oor.into()),
                }
            }
        }
    }
}

pub mod __impls {
    macro_rules! impl_transcode_be_bytes {
        ($a:ty) => {
            impl $crate::conv::Encode for $a {
                fn write_to<U: $crate::conv::target::Target>(&self, buf: &mut U) -> usize {
                    buf.push_all(&self.to_be_bytes()) + buf.resolve_zero()
                }
            }

            impl $crate::conv::Decode for $a {
                #[inline(always)]
                fn parse<P: $crate::parse::Parser>(
                    p: &mut P,
                ) -> $crate::parse::error::ParseResult<Self> {
                    const N: usize = <$a as $crate::conv::len::FixedLength>::LEN;
                    p.take_fixed::<N>().map(<$a>::from_be_bytes)
                }
            }
        };
    }

    impl_transcode_be_bytes!(u8);
    impl_transcode_be_bytes!(i8);
    impl_transcode_be_bytes!(u16);
    impl_transcode_be_bytes!(i16);
    impl_transcode_be_bytes!(u32);
    impl_transcode_be_bytes!(i32);
    impl_transcode_be_bytes!(i64);
    impl_transcode_be_bytes!(u64);
}

#[cfg(test)]
mod tests {
    use crate::builder::{strict::StrictBuilder, Builder};
    use crate::hex;

    use super::*;

    fn encode_decode<U, const N: usize>(table: [(U, &'static str); N])
    where
        U: Encode + Decode + std::cmp::PartialEq + std::fmt::Debug,
    {
        for (u, enc) in table.iter() {
            assert_eq!(enc.to_owned(), u.encode::<StrictBuilder>().into_hex());
            assert_eq!(U::decode(hex!(*enc)), *u);
        }
    }

    #[test]
    fn u8_encode_decode() {
        const U8_CASES: [(u8, &'static str); 5] = [
            (0x00, "00"),
            (0x01, "01"),
            (0x7f, "7f"),
            (0x80, "80"),
            (0xff, "ff"),
        ];
        encode_decode(U8_CASES)
    }

    #[test]
    fn i8_encode_decode() {
        const I8_CASES: [(i8, &'static str); 5] = [
            (0x00, "00"),
            (0x01, "01"),
            (0x7f, "7f"),
            (-128, "80"),
            (-1, "ff"),
        ];
        encode_decode(I8_CASES)
    }

    #[test]
    fn u16_encode_decode() {
        const U16_CASES: [(u16, &'static str); 5] = [
            (0x0000, "0000"),
            (0x0001, "0001"),
            (0x7fff, "7fff"),
            (0x8000, "8000"),
            (0xffff, "ffff"),
        ];
        encode_decode(U16_CASES)
    }

    #[test]
    fn i16_encode_decode() {
        const I16_CASES: [(i16, &'static str); 5] = [
            (0x0000, "0000"),
            (0x0001, "0001"),
            (0x7fff, "7fff"),
            (-0x8000, "8000"),
            (-0x1, "ffff"),
        ];
        encode_decode(I16_CASES)
    }

    #[test]
    fn u30_encode_decode() {
        let cases: [(u30, &'static str); 3] = [
            (u30::from_value(0x0000_0000), "00000000"),
            (u30::from_value(0x0000_0001), "00000001"),
            (u30::from_value(0x3fff_ffff), "3fffffff"),
        ];
        encode_decode(cases)
    }

    #[test]
    fn i31_encode_decode() {
        let cases: [(i31, &'static str); 5] = [
            (i31::from_value(0x0000_0000), "00000000"),
            (i31::from_value(0x0000_0001), "00000001"),
            (i31::from_value(0x3fff_ffff), "3fffffff"),
            (i31::from_value(-0x4000_0000), "c0000000"),
            (i31::from_value(-1), "ffffffff"),
        ];
        encode_decode(cases)
    }
    #[test]
    fn i32_encode_decode() {
        const I32_CASES: [(i32, &'static str); 5] = [
            (0x0000_0000, "00000000"),
            (0x0000_0001, "00000001"),
            (0x7fff_ffff, "7fffffff"),
            (-0x8000_0000, "80000000"),
            (-0x1, "ffffffff"),
        ];
        encode_decode(I32_CASES)
    }

    #[test]
    fn i64_encode_decode() {
        const I64_CASES: [(i64, &'static str); 5] = [
            (0x0000000000000000, "0000000000000000"),
            (0x0000000000000001, "0000000000000001"),
            (0x7fffffffffffffff, "7fffffffffffffff"),
            (-0x8000000000000000, "8000000000000000"),
            (-0x1, "ffffffffffffffff"),
        ];
        encode_decode(I64_CASES)
    }

    #[test]
    fn short_high() {
        let short_high_cases: [(RangedInt<u8,256,257>, &'static str); 2] = [
            (RangedInt::from_value(0x00), "0x00"),
            (RangedInt::from_value(0x01), "0x01"),
        ];

        encode_decode(short_high_cases)
    }
}
