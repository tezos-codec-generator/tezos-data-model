extern crate bitvec;
extern crate num_bigint;
extern crate rug;

pub trait Zarith {
    fn deserialize(bytes: &[u8]) -> Self;
    fn serialize(&self) -> Vec<u8>;
}

macro_rules! impl_zarith {
    ($x:ident) => {
        impl $crate::Encode for $x {
            fn write_to<U: $crate::conv::target::Target>(&self, buf: &mut U) -> usize {
                buf.push_all(&mut <$x as $crate::zarith::Zarith>::serialize(self)) + $crate::resolve_zero!(buf)
            }
        }

        impl $crate::Decode for $x {
            fn parse<P: $crate::Parser>(p: &mut P) -> $crate::ParseResult<Self> {
                Ok(<$x as $crate::zarith::Zarith>::deserialize(
                    &p.get_self_terminating(|byte| byte & 0x80 == 0)?,
                ))
            }
        }
    };
}

pub mod n {
    use std::{convert::TryInto, fmt::Display, ops::Deref};

    use num_bigint::BigUint;
    use rug::ops::DivRounding;

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
    pub struct N(pub BigUint);

    impl Display for N {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
            <BigUint as Display>::fmt(&self.0, f)
        }
    }

    impl Into<BigUint> for N {
        fn into(self) -> BigUint {
            self.0
        }
    }

    impl<T> From<T> for N
    where
        BigUint: From<T>,
    {
        fn from(i: T) -> Self {
            Self(BigUint::from(i))
        }
    }

    macro_rules! impl_nat_coerce {
        ($src:ty) => {
            impl TryInto<$src> for N {
                type Error = <BigUint as TryInto<$src>>::Error;
                fn try_into(self) -> Result<$src, Self::Error> {
                    self.0.try_into()
                }
            }
        };
    }

    impl_nat_coerce!(u8);
    impl_nat_coerce!(u16);
    impl_nat_coerce!(u32);
    impl_nat_coerce!(u64);

    impl Deref for N {
        type Target = BigUint;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl crate::conv::len::Estimable for N {
        const KNOWN: Option<usize> = None;

        fn unknown(&self) -> usize {
            let n: usize = self.0.bits() as usize;
            n.div_ceil(7)
        }
    }

    impl crate::zarith::Zarith for N {
        fn deserialize(bytes: &[u8]) -> Self {
            let lo7: Vec<u8> = bytes.iter().map(|&b| b & 0x7f).collect();
            match BigUint::from_radix_le(&lo7, 0x80) {
                Some(nat) => Self(nat),
                None => panic!("from_bytes: conversion failed!"),
            }
        }

        fn serialize(&self) -> Vec<u8> {
            let mut ret = self.0.to_radix_le(0x80);
            let final_ix: usize = ret.len() - 1;

            // we unwrap the loop logic of setting the high bit of every byte
            // but the last, by pre-setting the high bit of the last byte and
            // toggling it over every byte in the buffer
            unsafe {
                let lastbyt = ret.get_unchecked_mut(final_ix);
                *lastbyt ^= 0x80;
            }

            for byt in ret.iter_mut() {
                *byt ^= 0x80
            }

            ret
        }
    }

    impl_zarith!(N);

    #[cfg(test)]
    mod test {
        use super::*;
        use crate::zarith::Zarith;

        static NAT: fn(u32) -> N = |i: u32| N(<u32 as Into<BigUint>>::into(i));

        #[test]
        fn nat_conv() {
            assert_eq!(NAT(0), N::deserialize(&[0x00u8]));
            assert_eq!(NAT(1), N::deserialize(&[0x01u8]));
            assert_eq!(NAT(128), N::deserialize(&[0x80, 0x01]));
        }
    }
}

pub mod z {
    use crate::zarith::Zarith;
    use std::{convert::TryInto, fmt::Display, ops::Deref};

    use num_bigint::{BigInt, BigUint, Sign};
    use rug::ops::DivRounding;

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
    pub struct Z(pub BigInt);

    impl Display for Z {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
            <BigInt as Display>::fmt(&self.0, f)
        }
    }

    impl<T> From<T> for Z
    where
        BigInt: From<T>,
    {
        fn from(i: T) -> Self {
            Self(BigInt::from(i))
        }
    }

    impl Into<BigInt> for Z {
        fn into(self) -> BigInt {
            self.0
        }
    }

    macro_rules! impl_int_coerce {
        ($src:ty) => {
            impl TryInto<$src> for Z {
                type Error = <BigInt as TryInto<$src>>::Error;
                fn try_into(self) -> Result<$src, Self::Error> {
                    self.0.try_into()
                }
            }
        };
    }
    impl_int_coerce!(i8);
    impl_int_coerce!(i16);
    impl_int_coerce!(i32);
    impl_int_coerce!(i64);

    impl_int_coerce!(u8);
    impl_int_coerce!(u16);
    impl_int_coerce!(u32);
    impl_int_coerce!(u64);

    impl Deref for Z {
        type Target = BigInt;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl crate::conv::len::Estimable for Z {
        const KNOWN: Option<usize> = None;

        fn unknown(&self) -> usize {
            let n: usize = self.0.bits() as usize;
            match n {
                0..=6 => 1,
                n => 1 + (n - 6).div_ceil(7),
            }
        }
    }

    impl Zarith for Z {
        fn deserialize(bytes: &[u8]) -> Self {
            let mut b_iter = bytes.iter();

            let &first = b_iter.next().unwrap();

            let sg = match first & 0x40u8 {
                0 => Sign::Plus,
                _ => Sign::Minus,
            };

            let bot6 = first & 0x3fu8;

            let lo7: Vec<u8> = b_iter.map(|&b| b & 0x7f).collect();

            match BigUint::from_radix_le(&lo7, 0x80) {
                Some(mut i) => {
                    i <<= 6;
                    i |= BigUint::from(bot6);
                    Self(BigInt::from_biguint(sg, i))
                }
                None => panic!("from_bytes: conversion failed!"),
            }
        }

        /*
        fn from_bytes(bytes: &[u8]) -> Self {
            let mut n: BigInt = BigUint::new(vec![0]);
            let mut bits: u32 = 0;

            if bytes.len() == 0 {
                panic!(
                    "int_big::Z::from_bytes: cannot parse empty byteslice as Zarith integer"
                );
            }

            for (ix, &byte) in bytes.iter().enumerate() {
                let val = byte & 0x7fu8;
                n |= BigUint::from(val) << bits;
                bits += 7;
                if byte == 0 && ix > 0 {
                    panic!("Unexpected trailing zero byte in Zarith natural byteslice");
                }
            }

            Self(n)
        }
        */

        fn serialize(&self) -> Vec<u8> {
            let (sg, mut abs) = self.0.clone().into_parts();

            let bot6 = abs.modpow(&BigUint::from(1u8), &BigUint::from(0x40u8));
            abs >>= 6;
            abs <<= 7;

            abs |= match sg {
                Sign::Minus => bot6 | BigUint::from(0x40u8),
                _ => bot6,
            };

            let mut ret = abs.to_radix_le(0x80);
            let final_ix: usize = ret.len() - 1;

            // we unwrap the loop logic of setting the high bit of every byte
            // but the last, by pre-setting the high bit of the last byte and
            // toggling it over every byte in the buffer
            unsafe {
                let lastbyt = ret.get_unchecked_mut(final_ix);
                *lastbyt ^= 0x80;
            }

            for byt in ret.iter_mut() {
                *byt ^= 0x80
            }

            ret
        }
    }

    impl_zarith!(Z);

    #[cfg(test)]
    mod test {
        use crate::{hex, Decode};

        use super::*;

        static INT: fn(i32) -> Z = |i: i32| Z(<i32 as Into<BigInt>>::into(i));

        #[test]
        fn int_conv() {
            assert_eq!(INT(0), Z::decode(hex!("00")));
            assert_eq!(INT(1), Z::decode(hex!("01")));
            assert_eq!(INT(64), Z::decode(hex!("8001")));
            assert_eq!(INT(-32), Z::decode(hex!("60")));
        }
    }
}
