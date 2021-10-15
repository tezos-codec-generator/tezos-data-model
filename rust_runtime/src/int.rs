use crate::conv::{Decode, Encode};
use crate::parse::byteparser::ToParser;
use std::convert::{TryFrom, TryInto};
use std::fmt::{Debug, Display};

pub trait Integral: Eq + Ord + Debug + Display + Copy + Into<i64> + TryFrom<i64> {}
impl Integral for u8 {}
impl Integral for i8 {}
impl Integral for i16 {}
impl Integral for u16 {}
impl Integral for u32 {}
impl Integral for i32 {}

#[derive(Debug)]
pub enum OutOfRange {
    Underflow { min: i64, val: i64 },
    Overflow { max: i64, val: i64 },
}

impl OutOfRange {
    pub fn restrict<T, U>(x: T, min: U, max: U) -> Result<T, Self>
    where
        T: Into<i64> + Copy,
        U: Into<i64>,
    {
        let min64: i64 = min.into();
        let max64: i64 = max.into();
        let val: i64 = x.into();
        if val < min64 {
            Err(Self::Underflow { min: min64, val })
        } else if val > max64 {
            Err(Self::Overflow { max: max64, val })
        } else {
            Ok(x)
        }
    }
}

impl Display for OutOfRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            &OutOfRange::Underflow { min, val } => write!(
                f,
                "Provided value (:= {}) less than RangedInt minimum bound (:= {})",
                val, min
            ),
            &OutOfRange::Overflow { max, val } => write!(
                f,
                "Provided value (:= {}) greater than RangedInt maximum bound (:= {})",
                val, max
            ),
        }
    }
}

impl<I, const MIN: i32, const MAX: i32> Into<i64> for RangedInt<I, MIN, MAX>
where
    I: Integral,
{
    fn into(self) -> i64 {
        self.val.into()
    }
}

impl<I, const MIN: i32, const MAX: i32> Into<i32> for RangedInt<I, MIN, MAX>
where
    I: Integral + Into<i32>,
{
    fn into(self) -> i32 {
        self.val.into()
    }
}

impl<I, const MIN: i32, const MAX: i32> TryFrom<i32> for RangedInt<I, MIN, MAX>
where
    I: Integral,
{
    type Error = OutOfRange;

    fn try_from(x: i32) -> Result<Self, Self::Error> {
        match I::try_from(i64::from(x)) {
            Ok(val) => OutOfRange::restrict(val, MIN, MAX).map(|val| Self { val }),
            Err(_) => OutOfRange::restrict(x, MIN, MAX)
                .map(|val| panic!("Incoherent range [{},{}] on {}", MIN, MAX, val)),
        }
    }
}

impl<I, const MIN: i32, const MAX: i32> TryFrom<u32> for RangedInt<I, MIN, MAX>
where
    I: Integral,
{
    type Error = OutOfRange;

    fn try_from(x: u32) -> Result<Self, Self::Error> {
        match I::try_from(i64::from(x)) {
            Ok(val) => OutOfRange::restrict(val, MIN, MAX).map(|val| Self { val }),
            Err(_) => OutOfRange::restrict(x, MIN, MAX)
                .map(|val| panic!("Incoherent range [{},{}] on {}", MIN, MAX, val)),
        }
    }
}

impl<I, const MIN: i32, const MAX: i32> Into<u32> for RangedInt<I, MIN, MAX>
where
    I: Integral + Into<u32>,
{
    fn into(self) -> u32 {
        self.val.into()
    }
}

impl<I, const MIN: i32, const MAX: i32> RangedInt<I, MIN, MAX>
where
    I: Integral,
{
    const SANITY: bool = MIN >= -0x4000_0000i32 && MAX <= 0x3fff_ffffi32 && MIN <= MAX;

    fn precheck() {
        if !Self::SANITY {
            panic!(
                "RangedInt: generic bounds exceed 31-bit signed integer range: [{}, {}] is invalid",
                MIN, MAX
            )
        }
    }

    pub fn new(val: I) -> Self {
        Self::precheck();
        if val.into() >= MIN.into() && val.into() <= MAX.into() {
            Self { val }
        } else {
            panic!(
                "RangedInt::new: argument value {} out of range [{}, {}]",
                val, MIN, MAX
            );
        }
    }
}

#[allow(non_camel_case_types)]
#[allow(dead_code)]
pub type u30 = RangedInt<u32, 0, 0x3fff_ffff>;

#[allow(non_camel_case_types)]
#[allow(dead_code)]
pub type i31 = RangedInt<i32, -0x4000_0000i32, 0x3fff_ffffi32>;

#[macro_export]
macro_rules! impl_encode_words {
    ($a:ty) => {
        impl Encode<Vec<u8>> for $a {
            fn encode(&self) -> Vec<u8> {
                self.to_be_bytes().to_vec()
            }
        }
    };
}
#[derive(PartialEq, PartialOrd, Eq, Ord, Debug, Clone, Copy)]
pub struct RangedInt<I, const MIN: i32, const MAX: i32>
where
    I: Eq + Ord + Debug + Display + Copy,
{
    val: I,
}

impl_encode_words!(u8);
impl_encode_words!(i8);
impl_encode_words!(u16);
impl_encode_words!(i16);
impl_encode_words!(u32);
impl_encode_words!(i32);
impl_encode_words!(i64);

impl Decode for u8 {
    fn decode<U: ToParser>(inp: U) -> Self {
        let p = inp.to_parser();
        p.get_u8().unwrap()
    }
}

impl Decode for i8 {
    fn decode<U: ToParser>(inp: U) -> Self {
        let p = inp.to_parser();
        p.get_i8().unwrap()
    }
}

impl Decode for u16 {
    fn decode<U: ToParser>(inp: U) -> Self {
        let p = inp.to_parser();
        p.get_u16().unwrap()
    }
}

impl Decode for i16 {
    fn decode<U: ToParser>(inp: U) -> Self {
        let p = inp.to_parser();
        p.get_i16().unwrap()
    }
}

impl Decode for i32 {
    fn decode<U: ToParser>(inp: U) -> Self {
        let p = inp.to_parser();
        p.get_i32().unwrap()
    }
}

impl Decode for u32 {
    fn decode<U: ToParser>(inp: U) -> Self {
        let p = inp.to_parser();
        p.get_u32().unwrap()
    }
}

impl Decode for i64 {
    fn decode<U: ToParser>(inp: U) -> Self {
        let p = inp.to_parser();
        p.get_i64().unwrap()
    }
}

impl<I, const MIN: i32, const MAX: i32> Encode<Vec<u8>> for RangedInt<I, MIN, MAX>
where
    I: Eq + Ord + Debug + Display + Copy + Encode<Vec<u8>> + Into<i64> + TryFrom<i64>,
    <I as TryFrom<i64>>::Error: std::fmt::Debug,
{
    fn encode(&self) -> Vec<u8> {
        let enc_val: I = if MIN > 0 {
            let val: i64 = (*self).val.into();
            let min: i64 = MIN.into();
            (val - min).try_into().unwrap()
        } else {
            (*self).val
        };
        enc_val.encode()
    }
}

impl<I, const MIN: i32, const MAX: i32> Decode for RangedInt<I, MIN, MAX>
where
    I: Integral + Decode,
    <I as TryFrom<i64>>::Error: std::fmt::Debug,
{
    fn decode<U: ToParser>(inp: U) -> Self {
        let p = inp.to_parser();
        let raw = I::decode(p);
        if MIN > 0 {
            let rval: i64 = raw.into() + i64::from(MIN);
            if rval > MAX.into() {
                panic!("RangedInt::decode: value parsed would exceed range-bounds: {} > MAX (:= {}) - MIN (:= {})", raw, MAX, MIN)
            }
            Self::new(rval.try_into().unwrap())
        } else {
            if raw.into() < MIN.into() {
                panic!("RangedInt::decode: value parsed would underflow minimum range-bound: {} < MIN (:= {})", raw, MIN)
            } else if raw.into() > MAX.into() {
                panic!("RangedInt::decode: value parsed would overflow maximum range-bound: {} > MAX (:= {})", raw, MAX)
            } else {
                Self::new(raw)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::hex;
    use crate::parse::hexstring::HexString;

    use super::*;

    fn encode_decode<U, const N: usize>(table: [(U, &'static str); N])
    where
        U: Encode<HexString> + Decode + std::cmp::PartialEq + std::fmt::Debug,
    {
        for (u, enc) in table.iter() {
            assert_eq!(enc.to_owned(), HexString::to_string(&u.encode()));
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
            (u30::new(0x0000_0000), "00000000"),
            (u30::new(0x0000_0001), "00000001"),
            (u30::new(0x3fff_ffff), "3fffffff"),
        ];
        encode_decode(cases)
    }

    #[test]
    fn i31_encode_decode() {
        let cases: [(i31, &'static str); 5] = [
            (i31::new(0x0000_0000), "00000000"),
            (i31::new(0x0000_0001), "00000001"),
            (i31::new(0x3fff_ffff), "3fffffff"),
            (i31::new(-0x4000_0000), "c0000000"),
            (i31::new(-1), "ffffffff"),
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
}
