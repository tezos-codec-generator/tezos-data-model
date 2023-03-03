//! Oracle for the exact byte-length of the serialized form of a value
//!
//! This module contains the [`FixedLength`], [`ScalarLength`], and [`Estimable`]
//! hierarchy of traits, with `FixedLength ⊨ ScalarLength ⊨ Estimable`
//!
//! # `Estimable`
//!
//! The principal trait defined in this module is [`Estimable`], which in turn encompasses
//! (via blanket implementations) all types for which only `FixedLength` or `ScalarLength`
//! implementations are explicated. It encompasses the most general behavior required for
//! measuring the precise number of bytes in the serialized form of an encodable type, but
//! does not require that the type be encodable to implement, even there is little use in
//! implementing [`Estimable`] on non-[`Encode`](../trait.Encode.html) types.
//!
//! # FixedLength vs. ScalarLength
//!
//! `FixedLength` is the maximal refinement of `Estimable`, and requires the definition
//! of only item, an associated constant `LEN`, equal to the exact and invariant number of
//! bytes in the serialized form of all possible values of a particular type.
//!
//! A type is fixed-length if it satisfies any of the following descriptors
//! :
//!   * Types that are zero-width encoded, such as `()` (`LEN := 0`)
//!   * `Nullable<T>` where `T: FixedLength` with `T::LEN == 0` (`LEN := 0`, so this is recursive)
//!   * `Option<T>` where `T: FixedLength` with `T::LEN == 0` (`LEN := 1`)
//!   * bool (`LEN := 1`)
//!   * Fixed-precision numeric types `uX/iX/fX` (`LEN := X / 8`)
//!   * `RangedInt<T, _, _>` and `RangedFloat<_, _>` (as above)
//!   * `FixSeq<T, N>` where `T: FixedLength` (`LEN := N * T::LEN`)
//!   * `Padded<T, N>` where `T: FixedLength` (`LEN := N + T::LEN`)
//!   * `VPadded<T, N>` where `T: FixedLength` (`LEN := T::LEN`)
//!   * `Dynamic<S, T>` where `T: FixedLength` (`LEN := S::LEN + T::LEN`)
//!   * Enums defined using the `adt::cstyle` macro
//!   * Enums defined using the `adt:data` macro whose variant payload types are all of the same constant length
//!   * Any record or tuple, all of whose component types are fixed-length
//!
//! (Note that this is purely descriptive, and that implementations of `FixedLength` may not always
//! be provided or even possible for certain cases, as broader blanket implementations of `Estimable`
//! would be precluded).
//!
//! [`ScalarLength`] is a supertrait of [`FixedLength`] for types whose length is entirely scalar;
//! namely, the only variability in length is by adding or removing components of a constant fixed length,
//! and the number of such components can be queried cheaply.
//! In practice, this covers all types that are array-like over fixed-length elements, such as
//! `Vec<T: FixedLength>` and `String`. As there is very little room for user-definition of custom array-like
//! types within the schema, this is far less likely to be implemented directly by a consumer of this library.
//!
//! As there are blanket implementations of the form `impl<T: FixedLength> ScalarLength for T`
//! and `impl<T: ScalarLength> Estimable for T` included in this module, it is only necessary to define
//! the most specific refinement of `Estimable` for a custom type for all `Estimable` trait bounds to
//! be satisfiable and all `Estimable` methods to be usable. For blanket implementations where the
//! length of serialization includes the length of some generic type, it is recommended to blanket-implement
//! `Estimable` as it is the most general case.
//!
//! # Usage
//!
//! For the most part, these traits should not be hand-implemented without
//! precise knowledge of the codec format. This crate re-exports a
//! derive macro for `Estimable`, which generates implementations
//! of Estimable for locally defined structs, primarily used in codec modules
//! generated using the `codec_generator` project pipeline. This macro is also
//! used within the `adt::data` macro defined in this crate.
//!
//! # Estimable for Enums
//!
//! The [`adt`](crate::adt::self) module included in this crate provides the machinery necessary for
//! producing complete codecs for enumerated types, and the macros defined therein provide the appropriate
//! `Estimable`-entailing trait implementations in their expansion.
//!
//! While C-Style enums can be given the appropriate `FixedLength` implementation based on the underlying
//! byte-length of their codec representation, Data enums are difficult to properly optimize in cases where
//! pattern-matching on the constructor is not necessary, such as when all variants happen to have the same
//! invariant byte-length in the arguments of their undiscriminated payload. This is both difficult to determine
//! during codec generation, and difficult to produce the appropriate optimization for even when detected, and
//! may therefore yield less than ideal performance. Even still, it is expected that such underoptimized `Estimable::unknown`
//! implementations are fast enough compared to the other operations involved in serialization, that the marginal performance hit
//! is negligible in context.

/// Trait marking a type as having an invariant-length serializated form in the `data-encoding` binary codec

pub trait FixedLength {
    /// Invariant byte-length of the serialized forms of all possible values of `Self`
    const LEN: usize;
}

macro_rules! fix_length {
    ($n:expr, $($x:ty),+) => {
        $(impl FixedLength for $x {
            const LEN : usize = $n;
        })+
    };
}

fix_length!(0, ());
fix_length!(1, u8, i8, bool);
fix_length!(2, u16, i16);
fix_length!(4, u32, i32);
fix_length!(8, i64, u64, f64);

impl<T: FixedLength, const N: usize> FixedLength for [T; N] {
    const LEN: usize = N * T::LEN;
}

/// Trait associating a variable-length container type with its
/// element type `Elem: FixedLength`, and providing a consistent method for determining
/// the number of such elements in a given instance of the container type.
///
/// Also automatically implemented for all implementors of [`FixedLength`], in which case non-constant
/// methods are short-circuited to constant expressions, and `<Self as ScalarLength>::Elem = Self`.
pub trait ScalarLength {
    /// Override used for [`FixedLength`] types to allow for more efficient length-computations
    ///
    /// When blanket implemented via `FixedLength`, the value is overriden to `Some(<Self as FixedLength>::LEN)`
    const FIXED: Option<usize> = None;

    /// Constituent type of `Self` when marking a container type, or simply `Self` when blanket implemented via `FixedLength`
    type Elem: FixedLength;

    /// Invariant number of bytes required to serialize a single value of type `Self::Elem`
    const PER_ELEM: usize = <Self::Elem as FixedLength>::LEN;

    /// Returns the number of values of type `Self::Elem` contained (or constituted) by `self`
    ///
    /// If `Self::Elem = Self`, this should return `1`.
    fn n_elems(&self) -> usize;
}

impl<T: FixedLength> ScalarLength for T {
    const FIXED: Option<usize> = Some(T::LEN);

    type Elem = Self;

    /// Blanket implementation based on `FixedLength`
    /// that returns `1`
    fn n_elems(&self) -> usize {
        1
    }
}

/// Trait used to provide efficient and precise length-predictions for the binary serialization
/// of a type, to be used both for pre-determination of the length-prefix when serializing
/// `Dynamic` values, and when pre-allocating a large-enough buffer to write
/// the entire serialized form of a value without reallocation.
///
/// Does not necessitate that `Self: Encode`, but there is little benefit to be gained from
/// implementing this trait without a corresponding `Encode` implementation to optimize or
/// facilitate in doing so.
pub trait Estimable {
    /// Optional override indicating that the length is a constant value for all possible values of `Self`.
    ///
    /// While it would be safe enough to provide a default value of `None`, it is left to the implementor
    /// to provide an explicit `None` to make the determination that a type is not known-length as deliberate a process as possible.
    const KNOWN: Option<usize>;

    /// Infallible fallback that is used to determine the byte-length of the serialized form of a value on a case-by-case basis.
    fn unknown(&self) -> usize;

    /// Short-circuiting length function that returns the value of `Self::KNOWN`,
    /// or the evaluation of `self.unknown()` if the former is `None`.
    fn estimate(&self) -> usize {
        Self::KNOWN.unwrap_or_else(|| self.unknown())
    }
}

impl<T> Estimable for T
where
    T: ScalarLength,
{
    const KNOWN: Option<usize> = Self::FIXED;

    fn unknown(&self) -> usize {
        self.n_elems() * Self::PER_ELEM
    }
}

impl<T> Estimable for Option<T>
where
    T: Estimable,
{
    const KNOWN: Option<usize> = {
        match <T as Estimable>::KNOWN {
            Some(0) => Some(1),
            _ => None,
        }
    };

    fn unknown(&self) -> usize {
        match self {
            &None => 1,
            Some(x) => 1 + x.estimate(),
        }
    }
}

macro_rules! impl_scalar_len {
    ( $elt:ident ; $( $x:ty ),+ ) =>  {
        $(
            impl<$elt: FixedLength> ScalarLength for $x {
                type Elem = $elt;
                fn n_elems(&self) -> usize {
                    self.len()
                }
            }
        )+
    };
    ( $( $x:ty ),+ ) =>  {
        $(
            impl ScalarLength for $x {
                type Elem = u8;
                fn n_elems(&self) -> usize {
                    self.len()
                }
            }
        )+
    }
}

impl_scalar_len!(T; [T], &'_ [T], Vec<T>);
impl_scalar_len! { str, &'_ str, std::borrow::Cow<'_, str>, String }
