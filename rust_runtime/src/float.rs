use crate::bound::OutOfRange;
use crate::conv::len::FixedLength;
use crate::conv::{Decode, Encode};
use crate::parse::byteparser::ParseResult;
use crate::Parser;
use std::convert::TryFrom;
use std::fmt::Debug;


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

pub fn get_bounds<const MIN: u64, const MAX: u64>() -> (f64, f64) {
    (f64::from_bits(MIN), f64::from_bits(MAX))
}

impl<const MIN: u64, const MAX: u64> RangedFloat<MIN, MAX> {
    fn validate_bounds() -> (f64, f64) {
        let (min, max) = get_bounds::<MIN, MAX>();
        if !(min.is_normal() && max.is_normal() && min <= max) {
            panic!("RangedFloat<{},{}>: generic bounds are incoherent!", min, max)
        } else {
            (min, max)
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
        match OutOfRange::<f64>::restrict(raw, min, max) {
            Ok(val) => Ok(Self::new(val)),
            Err(oor) => Err(oor.into()),
        }
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
}
