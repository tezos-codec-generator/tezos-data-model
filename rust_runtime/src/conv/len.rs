//! Traits for determining the precise length of the serialized form of a value
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
//! implementing [`Estimable`] on non-[`Encode`](super::Encode) types.
//!
//! # FixedLength vs. ScalarLength
//!
//! [`FixedLength`] is the maximal refinement of [`Estimable`], and requires the definition
//! of only item, an associated constant `LEN`, equal to the exact and invariant number of
//! bytes in the serialized form of all possible values of a particular type. It necessarily
//! must be either a primitive type (`u*/i*/f*` numeric types, `bool`, `()`), or be a product-type
//! (anonymous tuple or struct) all of whose arguments are themselves FixedLength. Implementations
//! are only provided for a certain subset of primitives that are used in the `data-encoding` schema.
//!
//! (While it is technically possible to blanket-implement `FixedLength` for tuples all of whose argument
//! types are themselves implementors of FixedLength, doing so would only complicate the process of
//! generating codec modules for non-struct tuple codecs, as it would require an additional check to
//! ensure that adding a `#[derive(Estimable)]` attribute to the definition would not introduce conflicts
//! in cases when the codec type being defined would be covered by such a blanket implementation.)
//!
//! In contrast, [`ScalarLength`] is a relaxed supertrait of [`FixedLength`] whose only requirement
//! is that the serialized form of the type is precisely the concatenation of a variable but easily
//! calculable number of segments of heterogenous and invariant length. In practice, this covers
//! all types that are array-like, whether generic or monomorphic, such as `Vec<T: FixedLength>` and
//! `String`. As there is very little room for user-definition of custom array-like types within
//! the schema, this is far less likely to be implemented directly by a consumer of this library.
//!
//! As there are blanket implementations of the form `impl<T: FixedLength> ScalarLength for T`
//! and `impl<T: ScalarLength> Estimable for T` included in this module, it is only necessary to define
//! the most specific refinement of `Estimable` for a custom type for all `Estimable` trait bounds to
//! be satisfiable and all `Estimable` methods to be usable.
//!
//! # Usage
//!
//! For the most part, these traits should not be hand-implemented without precise
//! knowledge of the codec format. The [`estimable_derive`](::estimable_derive) crate
//! provides a derive macro for `Estimable`, which is used to provide boilerplate-free
//! implementations of Estimable for locally defined structs (without extant support for enums or unions)
//! in codec modules generated using the `codec_generator` project pipeline.
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

    fn n_elems(&self) -> usize {
        1
    }
}

/// Trait used to provide efficient and precise length-predictions for the binary serialization
/// of a type, to be used both for pre-determination of the length-prefix when serializing
/// [`Dynamic`][crate::dynamic::Dynamic] values, and when pre-allocating a large-enough buffer to write
/// the entire serialized form of a value without reallocation.
///
/// Does not necessitate that `Self: Encode`, but there is little benefit to be gained from
/// implementing this trait without a corresponding `Encode` implementation to optimize or facilitate in doing so.
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
    const KNOWN: Option<usize> = None;

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
