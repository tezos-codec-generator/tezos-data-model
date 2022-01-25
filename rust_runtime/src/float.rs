use crate::bound::OutOfRange;
use crate::conv::len::FixedLength;
use crate::conv::{Decode, Encode};
use crate::parse::byteparser::{ParseResult, Parser};
use std::convert::TryFrom;
use std::fmt::Debug;

#[macro_export]
macro_rules! ranged_float {
    ( $x:expr ) => {
        RangedFloat { val: $x }
    };
    ( $min:expr , $max:expr ) => {
        RangedFloat<{ unsafe { std::mem::transmute::<f64,u64>($min)} }, { unsafe { std::mem::transmute::<f64,u64>($max) } }>
    };
}

#[derive(PartialEq, PartialOrd, Debug, Clone, Copy)]
pub struct RangedFloat<const MIN: u64, const MAX: u64> {
    val: f64,
}

impl<const MIN: u64, const MAX: u64> Into<f64> for RangedFloat<MIN, MAX> {
    fn into(self) -> f64 {
        self.val
    }
}

impl<const MIN: u64, const MAX: u64> TryFrom<f32> for RangedFloat<MIN, MAX> {
    type Error = OutOfRange<f64>;

    fn try_from(x: f32) -> Result<Self, Self::Error> {
        OutOfRange::<f64>::restrict(x, f64::from_bits(MIN), f64::from_bits(MAX))
            .map(|val| Self { val: val as f64 })
    }
}

impl<const MIN: u64, const MAX: u64> TryFrom<f64> for RangedFloat<MIN, MAX> {
    type Error = OutOfRange<f64>;

    fn try_from(x: f64) -> Result<Self, Self::Error> {
        let (min, max) = get_bounds::<MIN, MAX>();
        OutOfRange::<f64>::restrict(x, min, max).map(|val| Self { val })
    }
}

pub const fn get_bounds<const MIN: u64, const MAX: u64>() -> (f64, f64) {
    unsafe { (std::mem::transmute(MIN), std::mem::transmute(MAX)) }
}

impl<const MIN: u64, const MAX: u64> RangedFloat<MIN, MAX> {
    fn validate_bounds() -> (f64, f64) {
        let (min, max): (f64, f64) = get_bounds::<MIN, MAX>();
        match (min.classify(), max.classify()) {
            (std::num::FpCategory::Nan, _) | (_, std::num::FpCategory::Nan) => {
                panic!("RangedFloat<{}, {}>: bounds cannot be NaN!", min, max)
            }
            (std::num::FpCategory::Infinite, _) | (_, std::num::FpCategory::Infinite) => {
                panic!("RangedFloat<{}, {}>: bounds cannot be infinite!", min, max)
            }
            _ => {
                if min > max {
                    panic!(
                        "RangedFloat<{min}, {max}>: {{ x | {min} <= x <= {max} }} is the empty set!",
                        min = min, max = max
                    )
                }
                (min, max)
            }
        }
    }

    pub fn new(val: f64) -> Self {
        let (min, max) = Self::validate_bounds();

        if val >= min && val <= max {
            Self { val }
        } else {
            panic!(
                "RangedFloat::new: argument value {} out of range [{}, {}]",
                val, min, max
            );
        }
    }

    pub(crate) fn get_validated(&self) -> f64 {
        let (min, max) = Self::validate_bounds();
        assert!(self.val <= max && self.val >= min);
        self.val
    }
}
impl Decode for f64 {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        Ok(f64::from_bits(<u64 as Decode>::parse(p)?))
    }
}

impl Encode for f64 {
    fn write(&self, buf: &mut Vec<u8>) {
        self.to_bits().write(buf)
    }
}

impl<const MIN: u64, const MAX: u64> Encode for RangedFloat<MIN, MAX> {
    fn write(&self, buf: &mut Vec<u8>) {
        self.get_validated().write(buf);
    }
}

impl<const MIN: u64, const MAX: u64> FixedLength for RangedFloat<MIN, MAX> {
    const LEN: usize = <u64 as FixedLength>::LEN;
}

impl<const MIN: u64, const MAX: u64> Decode for RangedFloat<MIN, MAX> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let raw = f64::parse(p)?;
        let (min, max) = Self::validate_bounds();
        Ok(Self::new(OutOfRange::<f64>::restrict(raw, min, max)?))
    }
}

#[cfg(test)]
mod tests {
    use crate::builder::{owned::OwnedBuilder, Builder};
    use crate::hex;

    use super::*;

    fn encode_decode<U, const N: usize>(table: [(U, &'static str); N])
    where
        U: Encode + Decode + std::cmp::PartialEq + std::fmt::Debug,
    {
        for (u, enc) in table.iter() {
            assert_eq!(enc.to_owned(), u.encode::<OwnedBuilder>().into_hex());
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
        const UNIT_CASES: [(ranged_float!(0.0, 1.0), &'static str); 4] = [
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
