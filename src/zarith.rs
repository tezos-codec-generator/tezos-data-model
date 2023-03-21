extern crate num_bigint;
extern crate num_integer;

trait Zarith {
    #[must_use]
    fn deserialize(bytes: impl IntoIterator<Item = u8>) -> Self;

    #[must_use]
    fn serialize(&self) -> Vec<u8>;
}

macro_rules! impl_zarith {
    ($x:ident) => {
        impl $crate::Encode for $x {
            fn write_to<U: $crate::conv::target::Target>(&self, buf: &mut U) -> usize {
                buf.push_all(&<$x as $crate::zarith::Zarith>::serialize(self))
                    + $crate::conv::target::Target::resolve_zero(buf)
            }
        }

        impl $crate::Decode for $x {
            fn parse<P: $crate::Parser>(p: &mut P) -> $crate::ParseResult<Self> {
                Ok(<$x as $crate::zarith::Zarith>::deserialize(
                    p.take_self_terminating(|byte| byte & 0x80 == 0)?,
                ))
            }
        }
    };
}

pub mod n {
    use std::{convert::TryFrom, fmt::Display, ops::Deref};

    use ::num_bigint::BigUint;
    use ::num_integer::Integer;

    #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Default)]
    #[repr(transparent)]
    pub struct N(pub BigUint);

    impl N {
        pub fn into_inner(self) -> BigUint {
            self.0
        }

        pub const fn as_inner(&self) -> &BigUint {
            &self.0
        }

        pub const fn new(nat: BigUint) -> Self {
            Self(nat)
        }
    }

    impl std::fmt::Debug for N {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, r#"ℕ({})"#, &self.0.to_string())
        }
    }

    impl Display for N {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
            <BigUint as Display>::fmt(&self.0, f)
        }
    }

    impl From<N> for BigUint {
        fn from(val: N) -> Self {
            val.0
        }
    }

    impl From<BigUint> for N {
        fn from(value: BigUint) -> Self {
            Self(value)
        }
    }

    macro_rules! impl_nat_coerce {
        ($src:ty) => {
            impl TryFrom<N> for $src {
                type Error = <$src as TryFrom<BigUint>>::Error;

                fn try_from(val: N) -> Result<$src, Self::Error> {
                    <$src as TryFrom<BigUint>>::try_from(val.0)
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
            Integer::div_ceil(&n, &7)
        }
    }

    impl super::Zarith for N {
        fn deserialize(bytes: impl IntoIterator<Item = u8>) -> Self {
            let lo7: Vec<u8> = bytes.into_iter().map(|b| b & 0x7f).collect();
            match BigUint::from_radix_le(&lo7, 0x80) {
                Some(nat) => Self(nat),
                None => panic!("from_bytes: conversion failed!"),
            }
        }

        fn serialize(&self) -> Vec<u8> {
            let mut ret = self.0.to_radix_le(0x80);

            // We simplify the loop logic below in which the high bit of every
            // byte but the last is set, by pre-emptively setting the high
            // bit of the final byte, and unconditionally toggling the high
            // bit in every loop iteration.
            match ret.last_mut() {
                Some(last) => *last ^= 0x80,
                None => unreachable!(),
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
            assert_eq!(NAT(0), N::deserialize([0x00u8]));
            assert_eq!(NAT(1), N::deserialize([0x01u8]));
            assert_eq!(NAT(128), N::deserialize([0x80, 0x01]));
        }
    }
}

pub mod z {
    use super::Zarith;
    use std::{convert::TryFrom, fmt::Display, ops::Deref};

    use ::num_bigint::{BigInt, BigUint, Sign};
    use ::num_integer::Integer;

    #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Default)]
    #[repr(transparent)]
    pub struct Z(pub BigInt);

    impl Z {
        pub fn into_inner(self) -> BigInt {
            self.0
        }

        pub const fn as_inner(&self) -> &BigInt {
            &self.0
        }

        pub const fn new(int: BigInt) -> Self {
            Self(int)
        }
    }

    impl std::fmt::Debug for Z {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "\u{2124}({})", &self.0.to_string())
        }
    }

    impl Display for Z {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
            <BigInt as Display>::fmt(&self.0, f)
        }
    }

    impl From<Z> for BigInt {
        fn from(val: Z) -> Self {
            val.0
        }
    }

    macro_rules! impl_int_coerce {
        ($src:ty) => {
            impl TryFrom<Z> for $src {
                type Error = <$src as TryFrom<BigInt>>::Error;
                fn try_from(val: Z) -> Result<$src, Self::Error> {
                    <$src as TryFrom<BigInt>>::try_from(val.0)
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
                n => 1 + Integer::div_ceil(&(n - 6), &7),
            }
        }
    }

    impl Zarith for Z {
        fn deserialize(bytes: impl IntoIterator<Item = u8>) -> Self {
            let mut b_iter = bytes.into_iter();

            let first = b_iter
                .next()
                .expect("Zarith::Z deserialization failed on empty input");

            let sg = match first & 0x40u8 {
                0 => Sign::Plus,
                _ => Sign::Minus,
            };

            let bot6 = first & 0x3fu8;

            let lo7: Vec<u8> = b_iter.map(|b| b & 0x7f).collect();

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

            // We initially shift by one, leaving an offset in the 6-group of
            // LSB in the first serialized byte, which will be corrected on its
            // own rather than require additional upfront BigUint arithmetic
            abs <<= 1u8;

            let mut ret = abs.to_radix_le(0x80);
            let final_ix: usize = ret.len() - 1;

            unsafe {
                let first_byte = ret.first_mut().unwrap_unchecked();

                *first_byte >>= 1u8;
                match sg {
                    Sign::Minus => *first_byte |= 0x40u8,
                    _ => {}
                };
            }

            // we unwrap the loop logic of setting the high bit of every byte
            // but the last, by pre-setting the high bit of the last byte and
            // toggling it over every byte in the buffer
            unsafe {
                let last_byte = ret.get_unchecked_mut(final_ix);
                *last_byte ^= 0x80;
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
        use crate::{hex, Decode, HexString, Encode};

        use super::*;

        static INT: fn(i32) -> Z = |i: i32| Z(<i32 as Into<BigInt>>::into(i));

        #[test]
        fn int_conv() {
            assert_eq!(INT(0), Z::decode(hex!("00")));
            assert_eq!(INT(0).encode::<HexString>(), hex!("00"));
            assert_eq!(INT(1), Z::decode(hex!("01")));
            assert_eq!(INT(1).encode::<HexString>(), hex!("01"));
            assert_eq!(INT(64), Z::decode(hex!("8001")));
            assert_eq!(INT(64).encode::<HexString>(), hex!("8001"));
            assert_eq!(INT(-32), Z::decode(hex!("60")));
            assert_eq!(INT(-32).encode::<HexString>(), hex!("60"));
        }
    }
}
