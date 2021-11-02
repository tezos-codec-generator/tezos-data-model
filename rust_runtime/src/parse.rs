pub mod errors {
    use std::fmt::*;

    #[derive(Debug, Clone)]
    pub enum ConvError<T> {
        ParityError(T),
        HexError(T),
    }

    impl Display for ConvError<String> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            match self {
                Self::ParityError(s) => {
                    write!(f, "input string has odd parity (expected even): '{}'", s)
                }
                Self::HexError(s) => {
                    write!(f, "input string is not all hexadecimal: '{}'", s)
                }
            }
        }
    }

    #[derive(Debug, Clone)]
    pub enum InternalErrorKind {
        ConsumeLengthMismatch { expected: usize, actual: usize },
        SliceCoerceFailure,
    }

    impl Display for InternalErrorKind {
        fn fmt(&self, f: &mut Formatter) -> Result {
            match self {
                InternalErrorKind::ConsumeLengthMismatch { expected, actual } => {
                    write!(
                        f,
                        "consume({}) returned slice of length {}",
                        expected, actual
                    )
                }
                InternalErrorKind::SliceCoerceFailure => {
                    write!(f, "failed to coerce from byte-slice to fixed-length array")
                }
            }
        }
    }

    #[derive(Debug, Clone)]
    pub enum ParseError {
        InternalError(InternalErrorKind),
        BufferOverflow {
            buflen: usize,
            offset: usize,
            requested: usize,
        },
        InvalidBoolean(u8),
    }

    impl Display for ParseError {
        fn fmt(&self, f: &mut Formatter) -> Result {
            match self {
                ParseError::BufferOverflow {
                    buflen,
                    offset,
                    requested,
                } => {
                    write!(f, "cannot increment offset by {} bytes (currently at byte {} in buffer of length {})", requested, offset, buflen)
                }
                ParseError::InternalError(err) => {
                    write!(f, "internal error ({})", err)
                }
                ParseError::InvalidBoolean(byte) => {
                    write!(f, "expected boolean := (0xff | 0x00), got 0x{:02x}", byte)
                }
            }
        }
    }
}

pub mod hexstring {
    use super::errors::ConvError::{self, HexError, ParityError};
    use crate::{builder::Builder, util::hex_of_bytes};
    use std::{borrow::Borrow, convert::TryFrom, vec::IntoIter};

    #[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
    pub struct HexString {
        words: Vec<u8>,
    }

    impl IntoIterator for HexString {
        type Item = u8;

        type IntoIter = IntoIter<u8>;

        fn into_iter(self) -> Self::IntoIter {
            self.words.into_iter()
        }
    }

    impl std::ops::Add<HexString> for HexString {
        type Output = HexString;

        fn add(self, rhs: HexString) -> Self::Output {
            let words: Vec<u8> = self.into_iter().chain(rhs.into_iter()).collect();
            Self { words }
        }
    }

    impl Borrow<[u8]> for HexString {
        fn borrow(&self) -> &[u8] {
            self.words.borrow()
        }
    }

    impl From<&[u8]> for HexString {
        fn from(words: &[u8]) -> Self {
            Self {
                words: words.to_vec(),
            }
        }
    }

    impl From<Vec<u8>> for HexString {
        fn from(words: Vec<u8>) -> Self {
            Self { words }
        }
    }

    impl TryFrom<&str> for HexString {
        type Error = ConvError<String>;

        fn try_from(s: &str) -> Result<Self, Self::Error> {
            let parity = s.len() % 2;

            if parity == 1 {
                return Err(ParityError(s.to_owned()));
            }

            let mut words: Vec<u8> = Vec::new();

            for wix in (0..s.len()).step_by(2) {
                match u8::from_str_radix(&s[wix..wix + 2], 16) {
                    Ok(byte) => words.push(byte),
                    Err(_) => return Err(HexError(s.to_owned())),
                }
            }

            Ok(HexString { words })
        }
    }

    #[macro_export]
    macro_rules! hex {
        ($s : expr) => {
            <HexString as std::convert::TryFrom<&str>>::try_from($s)
                .expect("hex! macro encountered error")
        };
    }

    impl Builder for HexString {
        fn word(b: u8) -> Self {
            Self { words: vec![b] }
        }

        fn words<const N: usize>(b: [u8; N]) -> Self {
            Self { words: b.to_vec() }
        }

        fn into_vec(self) -> Vec<u8> {
            self.words
        }
    }

    impl std::str::FromStr for HexString {
        type Err = super::errors::ConvError<String>;

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            Self::try_from(s)
        }
    }

    impl PartialEq<&str> for HexString {
        fn eq(&self, other: &&str) -> bool {
            <HexString as PartialEq<HexString>>::eq(self, &other.parse().unwrap())
        }
    }

    impl PartialEq<String> for HexString {
        fn eq(&self, other: &String) -> bool {
            <HexString as PartialEq<HexString>>::eq(self, &other.parse().unwrap())
        }
    }

    impl PartialEq<HexString> for String {
        fn eq(&self, other: &HexString) -> bool {
            <HexString as PartialEq<String>>::eq(other, &self)
        }
    }

    impl PartialEq<HexString> for &str {
        fn eq(&self, other: &HexString) -> bool {
            <HexString as PartialEq<&str>>::eq(other, self)
        }
    }

    impl HexString {
        pub fn get_words(&self) -> &[u8] {
            &self.words
        }

        pub fn iter(&self) -> std::slice::Iter<u8> {
            self.words.iter()
        }

        pub fn to_vec(self) -> Vec<u8> {
            self.words
        }

        pub fn as_hex(&self) -> String {
            hex_of_bytes(&self.words)
        }
    }

    impl std::fmt::Display for HexString {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            String::fmt(&self.as_hex(), f)
        }
    }
}

pub mod bytes {
    use crate::hex;

    use super::hexstring::HexString;

    pub struct ByteSlice<'a>(&'a [u8]);
    pub struct OwnedBytes(Vec<u8>);

    impl<'a> From<&'a [u8]> for ByteSlice<'a> {
        fn from(bytes: &'a [u8]) -> Self {
            Self(bytes)
        }
    }

    impl From<&[u8]> for OwnedBytes {
        fn from(bytes: &[u8]) -> Self {
            Self(bytes.to_owned())
        }
    }

    impl From<Vec<u8>> for OwnedBytes {
        fn from(bytes: Vec<u8>) -> Self {
            Self(bytes)
        }
    }

    impl<const N: usize> From<[u8; N]> for OwnedBytes {
        fn from(bytes: [u8; N]) -> Self {
            Self(bytes.to_vec())
        }
    }

    impl From<HexString> for OwnedBytes {
        fn from(hex: HexString) -> Self {
            OwnedBytes(hex.to_vec())
        }
    }

    impl From<&str> for OwnedBytes {
        fn from(s: &str) -> Self {
            hex!(s).into()
            // Bytes(s.as_bytes().to_owned())
        }
    }

    /* 
    impl<'a> ByteSlice<'a> {
        pub unsafe fn take(&self, len: usize) -> (&'a [u8], Self) {
            (&self.0[..len], Self(&self.0[len..]))
        }

        pub unsafe fn pop(&self) -> (u8, Self) {
            (self.0[0], Self(&self.0[1..]))
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }
    }
    */

    impl OwnedBytes {
        pub unsafe fn get_slice(&self, ix: usize, len: usize) -> &[u8] {
            &self.0[ix..ix + len]
        }

        pub unsafe fn get_word(&self, ix: usize) -> &u8 {
            &self.0[ix]
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }
    }
}

pub mod byteparser {
    use crate::parse::errors::InternalErrorKind;

    use super::bytes::OwnedBytes;
    use super::errors::ParseError;
    use std::cell::Cell;
    use std::convert::{TryFrom, TryInto};
    use std::ops::Deref;

    pub type ParseResult<T> = Result<T, ParseError>;

    pub struct ByteParser {
        _buf: OwnedBytes,
        _offset: Cell<usize>,
    }

    impl ByteParser {
        pub fn parse<T>(input: T) -> Self
        where
            OwnedBytes: TryFrom<T>,
            <T as TryInto<OwnedBytes>>::Error: std::fmt::Display,
        {
            match OwnedBytes::try_from(input) {
                Ok(_buf) => Self {
                    _buf,
                    _offset: Cell::new(0usize),
                },
                Err(e) => panic!("ByteParser::parse: error encountered: {}", e),
            }
        }
    }

    impl ByteParser {
        fn next(&self) -> Option<&u8> {
            let cur: usize = self._offset.get();
            let tgt = cur + 1;

            if tgt > self._buf.len() {
                None
            } else {
                Some(unsafe {
                    let ret = self._buf.get_word(cur);
                    self._offset.set(tgt);
                    ret
                })
            }
        }

        fn consume(&self, nbytes: usize) -> ParseResult<&[u8]> {
            let cur: usize = self._offset.get();

            let tgt = cur + nbytes;

            if cur + nbytes > self._buf.len() {
                Err(ParseError::BufferOverflow {
                    offset: cur,
                    requested: nbytes,
                    buflen: self._buf.len(),
                })
            } else {
                Ok(unsafe {
                    let ret = self._buf.get_slice(cur, nbytes);
                    self._offset.set(tgt);
                    ret
                })
            }
        }
    }

    impl ByteParser {
        pub fn get_u8(&self) -> ParseResult<u8> {
            match self.next() {
                Some(&byte) => Ok(byte),
                None => Err(ParseError::BufferOverflow {
                    buflen: self._buf.len(),
                    requested: 1,
                    offset: self._offset.get(),
                }),
            }
        }

        pub fn get_i8(&self) -> ParseResult<i8> {
            match self.next() {
                Some(&byte) => Ok(byte as i8),
                None => Err(ParseError::BufferOverflow {
                    buflen: self._buf.len(),
                    requested: 1,
                    offset: self._offset.get(),
                }),
            }
        }
    }

    impl ByteParser {
        fn consume_arr<const N: usize>(&self) -> ParseResult<[u8; N]> {
            let ret = self.consume(N);
            match ret {
                Err(e) => Err(e),
                Ok(bytes) => bytes.try_into().or(Err(ParseError::InternalError(
                    InternalErrorKind::SliceCoerceFailure,
                ))),
            }
        }
    }

    impl ByteParser {
        pub fn get_u16(&self) -> ParseResult<u16> {
            self.consume_arr::<2>().map(u16::from_be_bytes)
        }

        pub fn get_i16(&self) -> ParseResult<i16> {
            self.consume_arr::<2>().map(i16::from_be_bytes)
        }

        pub fn get_u32(&self) -> ParseResult<u32> {
            self.consume_arr::<4>().map(u32::from_be_bytes)
        }

        pub fn get_i32(&self) -> ParseResult<i32> {
            self.consume_arr::<4>().map(i32::from_be_bytes)
        }

        pub fn get_u64(&self) -> ParseResult<u64> {
            self.consume_arr::<8>().map(u64::from_be_bytes)
        }

        pub fn get_i64(&self) -> ParseResult<i64> {
            self.consume_arr::<8>().map(i64::from_be_bytes)
        }
    }

    impl ByteParser {
        pub fn get_bool(&self) -> ParseResult<bool> {
            match self.next() {
                Some(&byte) => match byte {
                    0xff => Ok(true),
                    0x00 => Ok(false),
                    _ => Err(ParseError::InvalidBoolean(byte)),
                },
                None => Err(ParseError::BufferOverflow {
                    buflen: self._buf.len(),
                    requested: 1,
                    offset: self._offset.get(),
                }),
            }
        }
    }

    impl ByteParser {
        pub fn get_dynamic(&self, nbytes: usize) -> ParseResult<Vec<u8>> {
            self.consume(nbytes).map(Vec::from)
        }

        pub fn get_fixed<const N: usize>(&self) -> ParseResult<[u8; N]> {
            self.consume_arr::<N>()
        }
    }

    pub trait ToParser {
        fn to_parser(self) -> ByteParser;
    }

    impl ToParser for ByteParser {
        fn to_parser(self) -> ByteParser {
            self
        }
    }

    impl<T> ToParser for T
    where
        OwnedBytes: TryFrom<T>,
        <T as TryInto<OwnedBytes>>::Error: std::fmt::Display,
    {
        fn to_parser(self) -> ByteParser {
            ByteParser::parse(self)
        }
    }

    impl<const N: usize> ToParser for &[u8; N] {
        fn to_parser(self) -> ByteParser {
            ByteParser::parse(self.to_vec())
        }
    }

    impl ToParser for String {
        fn to_parser(self) -> ByteParser {
            ByteParser::parse(self.deref())
        }
    }
}
