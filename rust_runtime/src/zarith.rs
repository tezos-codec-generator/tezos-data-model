extern crate bitvec;
extern crate num_bigint;
extern crate rug;

use crate::{Decode, Encode, Parser};

pub trait Zarith {
    fn deserialize(bytes: &[u8]) -> Self;
    fn serialize(&self) -> Vec<u8>;
}

impl<I: Zarith> Encode for I {
    fn write(&self, buf: &mut Vec<u8>) {
        buf.append(&mut self.serialize())
    }
}

impl<I: Zarith> Decode for I {
    fn parse<P: Parser>(p: &mut P) -> Self {
        I::deserialize(
            &p.get_self_terminating(|byte| byte & 0x80 == 0)
                .expect("<impl Zarith as Decode>::parse: error encountered"),
        )
    }
}

pub mod n {
    pub mod nat_big {
        use std::{convert::TryInto, fmt::Display, ops::Deref};

        use num_bigint::BigUint;

        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
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

    pub mod nat_rug {
        use crate::zarith::Zarith;
        use bitvec::order::Lsb0;
        use bitvec::prelude::BitVec;
        use bitvec::slice::BitSlice;
        use bitvec::view::BitView;
        use rug::Integer;
        use std::convert::{TryFrom, TryInto};
        use std::fmt::{Debug, Display};
        use std::ops::Deref;

        #[derive(Debug)]
        pub enum NatError {
            NonNatural(Integer),
        }

        impl Display for NatError {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    NatError::NonNatural(i) => write!(
                        f,
                        "Cannot construct Zarith Natural from negative integer: `{}`",
                        i
                    ),
                }
            }
        }

        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub struct N(pub Integer);

        impl Display for N {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                <Integer as Display>::fmt(&self.0, f)
            }
        }

        impl TryFrom<Integer> for N {
            type Error = NatError;

            fn try_from(i: Integer) -> Result<Self, Self::Error> {
                if i < Integer::from(0) {
                    Err(NatError::NonNatural(i))
                } else {
                    Ok(Self(i))
                }
            }
        }

        macro_rules! impl_nat_coerce {
            ($src:ty) => {
                impl From<$src> for N {
                    fn from(i: $src) -> Self {
                        Self(Integer::from(i))
                    }
                }

                impl TryInto<$src> for N {
                    type Error = <Integer as TryInto<$src>>::Error;
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

        impl Into<Integer> for N {
            fn into(self) -> Integer {
                self.0
            }
        }

        impl Deref for N {
            type Target = Integer;

            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl Zarith for N {
            fn deserialize(bytes: &[u8]) -> Self {
                let mut bits: BitVec<Lsb0, u8> = BitVec::with_capacity(bytes.len() * 7);

                // we assume implicitly that the input is terminated properly
                for &byte in bytes {
                    bits.extend_from_bitslice(&byte.view_bits::<Lsb0>()[0..7]);
                }

                Self(Integer::from_digits(
                    &bits.into_vec(),
                    rug::integer::Order::Lsf,
                ))
            }

            fn serialize(&self) -> Vec<u8> {
                let n_bits: u32 = self.0.significant_bits();

                if n_bits == 0 {
                    return vec![0u8];
                }

                let n_alloc: u32 = n_bits * 8 / 7;

                let mut bits: BitVec<Lsb0, u8> = BitVec::with_capacity(n_alloc as usize);

                let limbs: &[u64] = self.0.as_limbs();
                let limbits =
                    BitSlice::<Lsb0, u64>::from_slice(limbs).expect("limbs into bits failure");

                let (limbytes, _): (&BitSlice<Lsb0, u8>, &_) = unsafe {
                    let (_, temp, _) = limbits.align_to();
                    temp.split_at(n_bits as usize)
                };

                let mut lo7s = limbytes.chunks_exact(7);

                while let Some(lo7) = lo7s.next() {
                    bits.extend_from_bitslice(lo7);
                    bits.push(true);
                }

                let last = lo7s.remainder();
                if last.is_empty() {
                    *bits.last_mut().unwrap() = false;
                } else {
                    bits.extend_from_bitslice(last);
                }

                bits.into_vec()
            }
        }

        #[cfg(test)]
        mod test {
            use crate::{hex, Decode, Encode, HexString};

            use super::*;

            static NAT: fn(u32) -> N = |i: u32| N(<u32 as Into<Integer>>::into(i));

            fn roundtrip(preimage: u32, image: &'static str) {
                assert_eq!(NAT(preimage), N::decode(hex!(image)));
                assert_eq!(hex!(image), N::encode::<HexString>(&NAT(preimage)));
            }

            #[test]
            fn nat_conv() {
                roundtrip(0, "00");
                roundtrip(1, "01");
                roundtrip(128, "8001");
            }
        }
    }
}

pub mod z {
    pub mod int_big {
        use crate::zarith::Zarith;
        use std::{convert::TryInto, fmt::Display, ops::Deref};

        use num_bigint::{BigInt, BigUint, Sign};

        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
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

        #[cfg(test)]
        mod test {
            use crate::{hex, Decode, HexString};

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

    pub mod int_rug {
        use crate::zarith::Zarith;
        use rug::ops::DivRounding;
        use rug::Integer;
        use std::convert::TryInto;
        use std::fmt::{Debug, Display};
        use std::ops::{Add, Deref};

        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub struct Z(pub Integer);

        impl Display for Z {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                <Integer as Display>::fmt(&self.0, f)
            }
        }

        impl From<Integer> for Z {
            fn from(i: Integer) -> Self {
                Self(i)
            }
        }

        impl Into<Integer> for Z {
            fn into(self) -> Integer {
                self.0
            }
        }

        impl Deref for Z {
            type Target = Integer;

            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        macro_rules! impl_nat_coerce {
            ($src:ty) => {
                impl From<$src> for Z {
                    fn from(i: $src) -> Self {
                        Self(Integer::from(i))
                    }
                }

                impl TryInto<$src> for Z {
                    type Error = <Integer as TryInto<$src>>::Error;
                    fn try_into(self) -> Result<$src, Self::Error> {
                        self.0.try_into()
                    }
                }
            };
        }

        impl_nat_coerce!(u8);
        impl_nat_coerce!(i8);
        impl_nat_coerce!(u16);
        impl_nat_coerce!(i16);
        impl_nat_coerce!(u32);
        impl_nat_coerce!(i32);
        impl_nat_coerce!(u64);
        impl_nat_coerce!(i64);

        impl Zarith for Z {
            /*
            use bitvec::prelude::BitVec;
            use bitvec::slice::BitSlice;
            use bitvec::store::BitStore;
            use bitvec::view::BitView;

                pub fn from_bytes_direct(bytes: &[u8]) -> Self {
                    let mut bits : BitVec = BitVec::new();
                    let mut is_last = false;
                    let mut byte_iter = bytes.iter();

                    while !is_last {
                        if let Some(&byt) = byte_iter.next() {
                            let &bb  = byt.view_bits();
                            let (&val, &msb) = bb.split_at(7);
                            is_last = msb[0] == 0;
                            bits.extend_from_bitslice(val);
                        }
                    }
                }
                */

            fn deserialize(bytes: &[u8]) -> Self {
                let mut n: Integer =
                    Integer::with_capacity((bytes.len().saturating_sub(6)) * 7 + 1);
                let mut bits: u32 = 0;

                if bytes.len() == 0 {
                    panic!();
                }

                let mut b_iter = bytes.iter();

                let &first = b_iter.next().expect(
                    "int__rug::Z::from_bytes: cannot parse empty byteslice as Zarith integer",
                );

                let is_neg = (first & 0x40u8) != 0;
                let val = first & 0x3fu8;
                n |= Integer::from(val);
                bits += 6;

                for &byte in b_iter {
                    let val = byte & 0x7fu8;
                    n |= Integer::from(val) << bits;
                    bits += 7;
                    if byte == 0 {
                        panic!("Unexpected trailing zero byte in Zarith integral byteslice");
                    }
                }

                if is_neg {
                    Self(-n)
                } else {
                    Self(n)
                }
            }

            fn serialize(&self) -> Vec<u8> {
                let n_bytes: u32 = self
                    .0
                    .significant_bits()
                    .saturating_sub(6)
                    .div_ceil(7)
                    .add(1);
                let mut ret: Vec<u8> = Vec::with_capacity(n_bytes as usize);
                let mut nn: Integer = self.0.clone();

                let sign_mask = if nn < 0 { 0x40u8 } else { 0x0u8 };
                nn.abs_mut();

                let mut byte: u8 = (nn.to_u8_wrapping() & 0x3f) | sign_mask;
                nn >>= 6;
                let mut is_last = nn == 0;
                if !is_last {
                    byte |= 0x80u8;
                }
                ret.push(byte);

                const MASK: u8 = 0x7fu8;

                while !is_last {
                    let mut byte: u8 = nn.to_u8_wrapping() & MASK;
                    nn >>= 7;
                    is_last = nn == 0;
                    if !is_last {
                        byte |= 0x80u8;
                    }
                    ret.push(byte);
                }

                ret
            }
        }

        #[cfg(test)]
        mod test {
            use crate::{hex, Decode, HexString};

            use super::*;

            static INT: fn(u32) -> Z = |i: u32| Z(<u32 as Into<Integer>>::into(i));

            #[test]
            fn int_conv() {
                assert_eq!(INT(0), Z::decode(hex!("00")));
                assert_eq!(INT(1), Z::decode(hex!("01")));
                assert_eq!(INT(64), Z::decode(hex!("8001")));
            }
        }
    }
}
