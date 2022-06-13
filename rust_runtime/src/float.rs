//! Full-range and range-restricted floating point implementations
//!
//! This module provides both the boilerplate implementations required
//! for using raw `f64` values in codecs, as well as the type definition
//! and associated implementations for the `RangedFloat<MIN, MAX>` type,
//! which represents IEEE-754 double-precision floating-point numbers
//! restricted to a pre-determined range.
//!
//! As `f64` cannot be used as the type of `const` generics, `u64` is
//! the actual type of the `MIN` and `MAX` parameters, and represents
//! the bit-pattern, not the numeric value, of the lower and upper
//! bounds for the type's value, respectively. Furthermore, as
//! [`f64::to_bits`][tobits] and [`f64::from_bits`][frombits] are
//! not `const` in stable builds (Cf. Issue [#72447][issue]),
//! `std::mem::transmute` is used throughout this module instead.
//! This use is limited to bit-level casts between `u64` and `f64`,
//! which is implicitly safe.
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

/// Safely transmutes the bits of an `f64` value into an `u64` value for use in
/// generic const bounds of `RangedInt<MIN, MAX>` type signatures.
#[inline(always)]
pub const fn to_const_generic(bound: f64) -> u64 {
    unsafe { std::mem::transmute::<f64, u64>(bound) }
}

/// Safely restores the original `f64` value that has been transmuted into `u64`
/// for use in generic const bounds of `RangedInt<MIN, MAX>` type signatures.
#[inline(always)]
pub const fn from_const_generic(bound: u64) -> f64 {
    unsafe { std::mem::transmute::<u64, f64>(bound) }
}

/// Macro for writing `RangedFloat` with `f64`-typed bounds
///
/// Without this macro writing any particular type signature involving
/// `RangedFloat<MIN,MAX>` would require the caller to either somehow know the
/// IEEE-754 bit-sequence of the bounds they wished to enforce, or make a call
/// to a const function that performs a conversion from `f64` to `u64`
///
/// This macro simplifies the process by taking in two arguments, which are
/// interpreted as constant floating-point expressions, which are then converted
/// as `f64` into `u64` through a bitwise transmute operation.
///
/// As an alternative, the standalone function [`to_const_generic`] is provided,
/// for performing this transmute at the caller's discretion.
///
/// # Syntax
///
/// The syntax of this macro is identical to `RangedFloat`, but with any macro-invocation
/// delimiter pair ( `()`, `[]`, `{}` ) instead of angle-brackets (`<>`):
///
/// ```
/// # use ::rust_runtime::RangedF64;
/// assert_eq!(<RangedF64!(f64::MIN, f64::MAX)>::MIN_F64, f64::MIN);
/// ```
///
/// # Examples
/// ```
/// # use ::rust_runtime::RangedF64;
/// assert_eq!(f64::default(), <RangedF64!(-0.1,0.1) as Default>::default().as_f64());
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
/// Both bounds are included within the legal range.
///
/// It is not considered sound for either the upper or lower bound to be
/// non-finite or NaN. Using such bounds may lead to unexpected behavior.
///
/// # Specifying Bounds
///
/// The ideal way to represent `f64`-valued lower bound and upper bound on a
/// `RangedFloat` type would be as `const MIN: f64, const MAX: f64`.
///
/// However, due to the restrictions on what types may be used as const
/// generics, `f64` cannot be used.
///
/// Instead, the approach taken by this implementation is to use `const MIN_U64:
/// u64, const MAX_U64: u64` instead, as that is both legal, and there is a
/// one-to-one mapping between `u64` and `f64` through bit-level transmutation.
///
/// This is less than ideal, however, when any code working with `RangedFloat`
/// values is required to specify `MIN_U64` and `MAX_U64` explicitly.
///
/// As a workaround, two approaches are currently offered: the crate-level macro
/// [`RangedF64`], which takes the `MIN` and `MAX` parameters (in that order) as
/// constant-valued floating point expressions, and performs the transmutation
/// internally.
///
/// Beyond this, it is also possible to use the standalone function
/// [`to_const_generic`] (and, in the other direction, [`from_const_generic`])
/// to freely map between the intended interpretation, and the actual
/// representation, of the lower and upper bounds of `RangedFloat` types.
#[derive(PartialEq, PartialOrd, Debug, Clone, Copy)]
#[repr(transparent)]
pub struct RangedFloat<const MIN_U64: u64, const MAX_U64: u64> {
    val: f64,
}

impl<const MIN_U64: u64, const MAX_U64: u64> Default for RangedFloat<MIN_U64, MAX_U64> {
    /// Returns the closest legal value of `RangedFloat<MIN, MAX>` to
    /// `f64::default` (:= `0.0`).
    ///
    /// If the default value of `f64` is below the lower bound,
    /// the returned value is `MIN_
    ///
    /// nearer bound is returned. Otherwise the default value is returned,
    /// wrapped.
    fn default() -> Self {
        let val = <f64 as Default>::default().clamp(Self::MIN_F64, Self::MAX_F64);
        Self { val }
    }
}

impl<const MIN_U64: u64, const MAX_U64: u64> RangedFloat<MIN_U64, MAX_U64> {
    /// The lower bound associated with a `RangedFloat`, as a raw `f64`
    pub const MIN_F64: f64 = unsafe { std::mem::transmute::<u64, f64>(MIN_U64) };

    /// The upper bound associated with a `RangedFloat`, as a raw `f64`
    pub const MAX_F64: f64 = unsafe { std::mem::transmute::<u64, f64>(MAX_U64) };

    /// The smallest valid value of a `RangedFloat`, numerically equal to [`MIN_F64`]
    pub const MIN: Self = Self { val: Self::MIN_F64 };

    /// The largest valid value of a `RangedFloat`, numerically equal to [`MAX_F64`]
    pub const MAX: Self = Self { val: Self::MAX_F64 };


    /// Construct a `RangedFloat` that is numerically equal to `val`, without
    /// checking that it is in the valid range, or that the specified range
    /// is coherent.
    ///
    /// # Safety
    ///
    /// This function does not call any unsafe methods, but it can be used
    /// to violate the invariants on the type. It should only be used
    /// when the argument is already known to fall in the valid range.
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
            val: BoundsError::restrict_float(val, Self::MIN_F64, Self::MAX_F64)?,
        })
    }

    /// Constructs a `RangedFloat` that is numerically equal to `val`,
    /// provided that it is in range.
    pub fn from_f64(val: f64) -> Self {
        assert!(val >= Self::MIN_F64 && val <= Self::MAX_F64);
        Self { val }
    }

    /// Destructs a borrowed `RangedFloat` into a numerically equivalent `f64`
    ///
    /// Does not check that the value is in range, as this condition is typically
    /// enforced during the creation of a `RangedFloat`.
    #[inline]
    #[must_use]
    pub const fn as_f64(&self) -> f64 {
        self.val
    }

    pub fn prevalidate_f64(val: f64) -> Result<f64, BoundsError<f64>> {
        BoundsError::restrict_float(val, Self::MIN_F64, Self::MAX_F64)
    }

    pub fn prevalidate_f32(val: f32) -> Result<f64, BoundsError<f64>> {
        BoundsError::restrict_float(val, Self::MIN_F64, Self::MAX_F64)
    }
}

impl<const MIN_U64: u64, const MAX_U64: u64> From<RangedFloat<MIN_U64, MAX_U64>> for f64 {
    fn from(val: RangedFloat<MIN_U64, MAX_U64>) -> Self {
        val.val
    }
}

impl<const MIN_U64: u64, const MAX_U64: u64> TryFrom<f32> for RangedFloat<MIN_U64, MAX_U64> {
    type Error = BoundsError<f64>;

    fn try_from(x: f32) -> Result<Self, Self::Error> {
        Ok(Self {
            val: BoundsError::<f64>::restrict(x, Self::MIN, Self::MAX)? as f64,
        })
    }
}

impl<const MIN_U64: u64, const MAX_U64: u64> TryFrom<f64> for RangedFloat<MIN_U64, MAX_U64> {
    type Error = BoundsError<f64>;

    fn try_from(x: f64) -> Result<Self, Self::Error> {
        Ok(Self {
            val: BoundsError::<f64>::restrict_float(x, Self::MIN_F64, Self::MAX_F64)?,
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
        self.to_bits().write_to(buf) + buf.resolve_zero()
    }
}

impl<const MIN: u64, const MAX: u64> Encode for RangedFloat<MIN, MAX> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.as_f64().write_to(buf) + buf.resolve_zero()
    }
}

impl<const MIN: u64, const MAX: u64> FixedLength for RangedFloat<MIN, MAX> {
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
