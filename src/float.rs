//! Floating-point codecs
//!
//! This module provides both the boilerplate implementations required
//! for using raw `f64` values in codecs, as well as the type definition
//! and associated implementations for the `RangedFloat<MIN_U64, MAX_U64>` type,
//! which represents IEEE-754 double-precision floating-point numbers
//! restricted to a pre-determined range.
//!
//! As `f64` cannot be used as the type of `const` generics, `u64` is
//! the actual type of the `MIN_U64` and `MAX_U64` parameters, and represents
//! the bit-pattern, not the numeric value, of the lower and upper
//! bounds for the type's value. Furthermore, as
//! [`f64::to_bits`][tobits] and [`f64::from_bits`][frombits] are
//! not `const` in stable builds (Cf. Issue [#72447][issue]),
//! `std::mem::transmute` is used sparingly within this module.
//! As this use is limited to bit-level casts between `u64` and `f64`,
//! such usages are determined to be sound and should never cause
//! undefined behavior.
//!
//! [tobits]: https://doc.rust-lang.org/std/primitive.f64.html#method.to_bits
//! [frombits]: https://doc.rust-lang.org/std/primitive.f64.html#method.from_bits
//! [issue]: https://github.com/rust-lang/rust/issues/72447

use crate::conv::len::FixedLength;
use crate::conv::target::Target;
use crate::conv::{Decode, Encode};
use crate::error::BoundsError;
use crate::parse::{ParseResult, Parser};
use std::convert::TryFrom;
use std::fmt::Debug;

/// Safely transmutes the bits of an `f64` value into a `u64` value
///
/// The primary purpose of this function and its dual, [`from_const_generic`],
/// is in const expressions related to the lower and upper bound parameters
/// of [`RangedInt<MIN_U64, MAX_U64>`].
#[inline(always)]
#[must_use]
pub const fn to_const_generic(bound: f64) -> u64 {
    unsafe { std::mem::transmute::<f64, u64>(bound) }
}

/// Safely transmutes the bits of a `u64` value into an `f64` value
///
/// The primary purpose of this function and its dual, [`to_const_generic`],
/// is in const expressions related to the lower and upper bound parameters
/// of [`RangedInt<MIN_U64, MAX_U64>`].
#[inline(always)]
#[must_use]
pub const fn from_const_generic(bound: u64) -> f64 {
    unsafe { std::mem::transmute::<u64, f64>(bound) }
}

/// Macro for writing `RangedFloat` signatures with `f64`-typed bounds
///
/// In the absence of this macro, specifying any type signature involving
/// [`RangedFloat<MIN, MAX>`] would require the caller to either
/// somehow know the IEEE-754 bit-sequence of the bounds they wished to
/// enforce, or to call to a const function that performs the necessary
/// bit-level conversion, such as [`to_const_generic`].
///
/// This macro simplifies the process by taking in two arguments, which are
/// implicitly interpreted as constant floating-point expressions.
/// The values of these expressions are then converted, as `f64`,
/// into the bitwise-equivalent `u64` value and used in the const generic
/// bounds of the `RangedFloat` type.
///
/// # Examples
///
/// Associated constants
///
/// In place of a concrete type signature:
///
/// ```
/// # use ::tedium::{RangedF64};
/// use std::f64::consts::{E, PI};
/// pub type FromEToPi = RangedF64!{E, PI};
/// ```
///
/// When qualifying type-associated consts:
///
/// ```
/// # use ::tedium::RangedF64;
/// assert_eq!(<RangedF64!(f64::MIN, f64::MAX)>::MIN_F64, f64::MIN);
/// ```
///
/// When fully qualifying trait methods on `RangedFloat`:
///
/// ```
/// # use ::tedium::RangedF64;
/// assert_eq!(f64::default(), *<RangedF64!(-0.1,0.1) as Default>::default().as_f64());
/// ```
///
#[macro_export]
macro_rules! RangedF64 {
    ( $min:expr , $max:expr ) => {
        $crate::float::RangedFloat<{ unsafe { std::mem::transmute::<f64, u64>($min) } }, { unsafe { std::mem::transmute::<f64, u64>($max) } }>
    };
}

/// Range-restricted `f64` values
///
/// This type represents double-precision floating-point values that are
/// restricted to fall within a particular range, which is determined statically
/// at the schema level and runtime-checked at the codec level.
///
/// Both the upper and lower bound-values are themselves included within the legal
/// range.
///
/// Neither bound should be `NaN`, and the upper bound must be greater than or
/// equal to the lower bound. It is also advised that only finite values be used
/// for bounds. None of these conditions can be statically precluded, but it is
/// nevertheless expected that they be upheld. Using any such bounds may lead
/// to unexpected behavior, though not necessarily undefined behavior.
///
/// # Specifying Bounds
///
/// The ideal way to represent `f64`-valued lower bound and upper bound on a
/// `RangedFloat` type would be as `const MIN: f64, const MAX: f64`.
///
/// However, due to the restrictions on what types may be used as const
/// generics, this is not achievable in the current stable release.
///
/// Instead, the approach taken by this implementation is to use `const MIN_U64:
/// u64, const MAX_U64: u64` instead, as that is both legal, and there is a
/// one-to-one mapping between `u64` and `f64` through bit-level transmutation.
///
/// In order to mitigate the impact of this design decision, this crate provides
/// a macro [`RangedF64`], which can be used to specify the bounds as floating
/// point values.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct RangedFloat<const MIN_U64: u64, const MAX_U64: u64> {
    val: f64,
}

impl<const MIN_U64: u64, const MAX_U64: u64> Default for RangedFloat<MIN_U64, MAX_U64> {
    /// Returns the closest legal value of `RangedFloat<MIN, MAX>` to
    /// `f64::default` (:= `0.0`).
    ///
    /// This will equal `0.0` if it is in the range `[MIN_F64, MAX_F64]`,
    /// and otherwise will return whichever of the two bounds are closest to
    /// `0.0`
    #[inline]
    #[must_use]
    fn default() -> Self {
        let val = 0.0f64.clamp(Self::MIN_F64, Self::MAX_F64);
        Self { val }
    }
}

impl<const MIN_U64: u64, const MAX_U64: u64> RangedFloat<MIN_U64, MAX_U64> {
    /// The lower bound associated with a `RangedFloat`, as a raw `f64`
    pub const MIN_F64: f64 = from_const_generic(MIN_U64);

    /// The upper bound associated with a `RangedFloat`, as a raw `f64`
    pub const MAX_F64: f64 = from_const_generic(MAX_U64);

    /// The smallest valid value of a `RangedFloat`, numerically equal to [`MIN_F64`]
    ///
    /// This definition relies on the static implementation of `RangedFloat`
    /// as a newtype around `f64`, marked as `#[repr(transparent)]`
    pub const MIN: Self = unsafe { Self::from_f64_unchecked(Self::MIN_F64) };

    /// The largest valid value of a `RangedFloat`, numerically equal to [`MAX_F64`]
    ///
    /// This definition relies on the static implementation of `RangedFloat`
    /// as a `#[repr(transparent)]`-annotated newtype around `f64`.
    pub const MAX: Self = unsafe { Self::from_f64_unchecked(Self::MAX_F64) };

    /// Construct a `RangedFloat` that is numerically equal to `val`, without
    /// checking that it is in-range, or that the range itself is coherent.
    ///
    /// # Safety
    ///
    /// This function is not expected to produce undefined behavior, but is marked
    /// as unsafe because it does not preclude the construction of invalid
    /// `RangedFloat` values. It should only be called on values that are already
    /// known or determined to be in-range.
    #[inline(always)]
    #[must_use]
    pub const unsafe fn from_f64_unchecked(val: f64) -> Self {
        Self { val }
    }

    /// Attempt to construct a `RangedFloat` that is numerically equal to `val`,
    /// provided that it is in range.
    ///
    /// Returns a `BoundsError` value indicating the nature of invalidity
    /// if `val < MIN_F64`, `val > MAX_F64`, `MIN_F64 > MAX_F64`, or any
    /// of `val`, `MIN_F64`, or `MAX_F64` are `NaN`.
    #[inline]
    pub fn try_from_f64(val: f64) -> Result<Self, BoundsError<f64>> {
        Ok(Self {
            val: Self::prevalidate_f64(val)?,
        })
    }

    /// Constructs a `RangedFloat` that is numerically equal to `val`,
    /// provided that it is in range.
    ///
    /// For efficiency, this method only determines validity, but does
    /// not distinguish between any of the conditions of invalidity.
    ///
    /// For a version of this method that does not panic, and properly
    /// distinguishes the types of invalidity causing failure, use
    /// [`try_from_f64`] instead.
    ///
    /// # Panics
    ///
    /// This method will panic if either of the predicates
    /// `val >= Self::MIN_F64` or `val <= Self::MAX_F64`
    /// are false, namely when `val` is out-of-bounds, the bounds
    /// are inverted (`MAX < MIN`), or any of those three values
    /// are `NaN`.
    pub fn from_f64(val: f64) -> Self {
        assert!(
            val >= Self::MIN_F64 && val <= Self::MAX_F64,
            "RangedFloat::from_f64 called on out-of-range argument"
        );
        Self { val }
    }

    /// Returns a reference to the `f64` value stored within a borrowed `RangedFloat`.
    ///
    /// Does not check that the value is in range, as this condition is typically
    /// enforced during the creation of a `RangedFloat`.
    #[inline]
    #[must_use]
    pub const fn as_f64(&self) -> &f64 {
        &self.val
    }

    /// Checks whether `val` is out-of-bounds, returning `Ok(val)` if it is
    /// legal and the appropriate error otherwise.
    ///
    /// # Errors
    ///
    /// Will return [`InvalidBounds`](crate::error::BoundsError::InvalidBounds) if `Self::MIN_F64 > Self::MAX_F64`.
    ///
    /// Will return [`Underflow`](crate::error::BoundsError::Underflow) if `val < Self::MIN_F64`.
    ///
    /// Will return [`Overflow`](crate::error::BoundsError::Overflow) if `val > Self::MAX_F64`.
    #[inline]
    pub fn prevalidate_f64(val: f64) -> Result<f64, BoundsError<f64>> {
        BoundsError::restrict_float(val, Self::MIN_F64, Self::MAX_F64)
    }

    /// Checks whether `val` is out-of-bounds, returning `Ok(val as f64)` if it is
    /// legal and the appropriate error otherwise.
    ///
    /// # Errors
    ///
    /// Will return [`InvalidBounds`](crate::error::BoundsError::InvalidBounds) if `Self::MIN_F64 > Self::MAX_F64`.
    ///
    /// Will return [`Underflow`](crate::error::BoundsError::Underflow) if `val < Self::MIN_F64`.
    ///
    /// Will return [`Overflow`](crate::error::BoundsError::Overflow) if `val > Self::MAX_F64`.
    #[inline]
    pub fn prevalidate_f32(val: f32) -> Result<f64, BoundsError<f64>> {
        BoundsError::restrict_float(val, Self::MIN_F64, Self::MAX_F64)
    }

    /// Checks whether an existing value `self` is valid, which may be
    /// useful in cases where the caller has either themselves created
    /// a `RangedFloat` value without bounds-checking, or wishes To
    /// ensure that a value they were not responsible for creating is
    /// not malformed.
    ///
    /// Returns `Ok(val)` where `val` is numerically equivalent to `self`,
    /// and is within the well-formed range `[MIN, MAX]`.
    ///
    /// # Errors
    ///
    /// Will return [`InvalidBounds`] if `Self::MIN_F64 > Self::MAX_F64`, or if either
    /// are `NaN`.
    ///
    /// Will return [`Underflow`] if `self < Self::MIN`.
    ///
    /// Will return [`Overflow`] if `self > Self::MAX`.
    ///
    /// If `self` contains a `NaN` value, the specific error is unspecified between
    /// `Underflow` and `Overflow`.
    ///
    /// [`Underflow`]: crate::error::BoundsError::Underflow
    /// [`Overflow`]: crate::error::BoundsError::Overflow
    /// [`InvalidBounds`]: crate::error::BoundsError::InvalidBounds
    #[inline]
    pub fn get_validated(&self) -> Result<f64, BoundsError<f64>> {
        BoundsError::restrict_float(self.val, Self::MIN_F64, Self::MAX_F64)
    }
}

impl<const MIN_U64: u64, const MAX_U64: u64> From<RangedFloat<MIN_U64, MAX_U64>> for f64 {
    #[inline]
    fn from(val: RangedFloat<MIN_U64, MAX_U64>) -> Self {
        val.val
    }
}

impl<const MIN_U64: u64, const MAX_U64: u64> TryFrom<f32> for RangedFloat<MIN_U64, MAX_U64> {
    type Error = BoundsError<f64>;

    #[inline]
    fn try_from(x: f32) -> Result<Self, Self::Error> {
        Ok(Self {
            val: Self::prevalidate_f32(x)?,
        })
    }
}

impl<const MIN_U64: u64, const MAX_U64: u64> TryFrom<f64> for RangedFloat<MIN_U64, MAX_U64> {
    type Error = BoundsError<f64>;

    #[inline]
    fn try_from(x: f64) -> Result<Self, Self::Error> {
        Ok(Self {
            val: Self::prevalidate_f64(x)?,
        })
    }
}

impl Decode for f64 {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        Ok(f64::from_bits(<u64 as Decode>::parse(p)?))
    }
}

impl Encode for f64 {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.to_bits().write_to(buf)
    }
}

impl<const MIN_U64: u64, const MAX_U64: u64> Encode for RangedFloat<MIN_U64, MAX_U64> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.as_f64().write_to(buf)
    }
}

impl<const MIN_U64: u64, const MAX_U64: u64> FixedLength for RangedFloat<MIN_U64, MAX_U64> {
    const LEN: usize = <u64 as FixedLength>::LEN;
}

impl<const MIN_U64: u64, const MAX_U64: u64> Decode for RangedFloat<MIN_U64, MAX_U64> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        Ok(Self::try_from_f64(f64::parse(p)?)?)
    }
}

#[cfg(test)]
mod tests {
    use crate::builder::{strict::StrictBuilder, Builder};
    use crate::hex;

    use super::*;

    macro_rules! ranged_float {
        ( $x:expr ) => {
            RangedFloat { val: $x }
        };
    }

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
    fn f64_encode_decode() {
        const F64_CASES: [(f64, &'static str); 4] = [
            (0.0_f64, "0000000000000000"),
            (1.0_f64, "3ff0000000000000"),
            (std::f64::consts::PI, "400921fb54442d18"),
            (std::f64::consts::E, "4005bf0a8b145769"),
        ];
        encode_decode(F64_CASES)
    }

    #[test]
    fn unit_encode_decode() {
        const UNIT_CASES: [(RangedF64!(0.0, 1.0), &'static str); 4] = [
            (ranged_float!(0.0), "0000000000000000"),
            (ranged_float!(1.0), "3ff0000000000000"),
            (
                ranged_float!(std::f64::consts::FRAC_1_PI),
                "3fd45f306dc9c883",
            ),
            (ranged_float!(std::f64::consts::LN_2), "3fe62e42fefa39ef"),
        ];
        encode_decode(UNIT_CASES)
    }
}
