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
        NonTerminating(Vec<u8>),
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
                },
                ParseError::InternalError(err) => {
                    write!(f, "internal error ({})", err)
                },
                ParseError::InvalidBoolean(byte) => {
                    write!(f, "expected boolean := (0xff | 0x00), got 0x{:02x}", byte)
                },
                ParseError::NonTerminating(buf) => {
                    write!(f, "self-terminating codec cut off (end-of-window encountered before terminating condition met): `{}`", crate::util::hex_of_bytes(buf))
                },
            }
        }
    }
}

pub mod hexstring {
    use super::errors::ConvError::{self, HexError, ParityError};
    use crate::{builder::Builder, util::hex_of_bytes};
    use std::{borrow::Borrow, convert::TryFrom, iter::FromIterator, vec::IntoIter};

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

    impl FromIterator<u8> for HexString {
        fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> Self {
            Self {
                words: iter.into_iter().collect::<Vec<u8>>(),
            }
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

        fn len(&self) -> usize {
            self.words.len()
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
            Self(hex.to_vec())
        }
    }

    impl From<&str> for OwnedBytes {
        fn from(s: &str) -> Self {
            // hex!(s).into()
            Self(s.as_bytes().to_owned())
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

        pub unsafe fn get_word(&self, ix: usize) -> u8 {
            self.0[ix]
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }
    }
}

pub mod byteparser {
    use crate::internal::{BoundAwareMarker, ContextOffset, Marker};
    use crate::parse::errors::InternalErrorKind;

    use super::bytes::OwnedBytes;
    use super::errors::ParseError;
    use std::convert::{TryFrom, TryInto};
    use std::ops::Deref;

    pub type ParseResult<T> = Result<T, ParseError>;

    pub trait Parser: Iterator<Item = u8> {
        fn len(&self) -> usize;

        fn offset(&self) -> usize;

        fn consume(&mut self, nbytes: usize) -> ParseResult<&[u8]>;

        fn set_fit(&mut self, n: usize);

        fn test_target(&mut self) -> bool;

        fn enforce_target(&mut self);

        fn consume_arr<const N: usize>(&mut self) -> ParseResult<[u8; N]> {
            let ret = self.consume(N);
            match ret {
                Err(e) => Err(e),
                Ok(bytes) => bytes.try_into().or(Err(ParseError::InternalError(
                    InternalErrorKind::SliceCoerceFailure,
                ))),
            }
        }

        fn get_u8(&mut self) -> ParseResult<u8> {
            match self.next() {
                Some(byte) => Ok(byte),
                None => Err(ParseError::BufferOverflow {
                    buflen: self.len(),
                    requested: 1,
                    offset: self.offset(),
                }),
            }
        }

        fn get_i8(&mut self) -> ParseResult<i8> {
            match self.next() {
                Some(byte) => Ok(byte as i8),
                None => Err(ParseError::BufferOverflow {
                    buflen: self.len(),
                    requested: 1,
                    offset: self.offset(),
                }),
            }
        }

        fn get_u16(&mut self) -> ParseResult<u16> {
            self.consume_arr::<2>().map(u16::from_be_bytes)
        }

        fn get_i16(&mut self) -> ParseResult<i16> {
            self.consume_arr::<2>().map(i16::from_be_bytes)
        }

        fn get_u32(&mut self) -> ParseResult<u32> {
            self.consume_arr::<4>().map(u32::from_be_bytes)
        }

        fn get_i32(&mut self) -> ParseResult<i32> {
            self.consume_arr::<4>().map(i32::from_be_bytes)
        }

        fn get_u64(&mut self) -> ParseResult<u64> {
            self.consume_arr::<8>().map(u64::from_be_bytes)
        }

        fn get_i64(&mut self) -> ParseResult<i64> {
            self.consume_arr::<8>().map(i64::from_be_bytes)
        }

        fn get_bool(&mut self) -> ParseResult<bool> {
            match self.next() {
                Some(byte) => match byte {
                    0xff => Ok(true),
                    0x00 => Ok(false),
                    _ => Err(ParseError::InvalidBoolean(byte)),
                },
                None => Err(ParseError::BufferOverflow {
                    buflen: self.len(),
                    requested: 1,
                    offset: self.offset(),
                }),
            }
        }

        fn get_dynamic(&mut self, nbytes: usize) -> ParseResult<Vec<u8>> {
            self.consume(nbytes).map(Vec::from)
        }

        fn get_fixed<const N: usize>(&mut self) -> ParseResult<[u8; N]> {
            self.consume_arr::<N>()
        }

        fn get_self_terminating<F>(&mut self, is_terminal: F) -> ParseResult<Vec<u8>>
        where
        F: Fn(u8) -> bool
        {
            let mut ret : Vec<u8> = Vec::with_capacity(self.len() - self.offset());
            loop {
                if let Some(byte) = self.next() {
                    ret.push(byte);
                    if is_terminal(byte) {
                        break Ok(ret)
                    }
                } else {
                    break Err(ParseError::NonTerminating(ret))
                }
            }
        }
    }

    pub struct ByteParser {
        buffer: OwnedBytes,
        offset: ContextOffset,
    }

    impl ByteParser {
        pub fn parse<T>(input: T) -> Self
        where
            OwnedBytes: TryFrom<T>,
            <T as TryInto<OwnedBytes>>::Error: std::fmt::Display,
        {
            match OwnedBytes::try_from(input) {
                Ok(buffer) => {
                    let offset = ContextOffset::new(buffer.len());
                    Self { buffer, offset }
                }
                Err(e) => panic!("ByteParser::parse: error encountered: {}", e),
            }
        }
    }

    impl Iterator for ByteParser {
        type Item = u8;

        fn next(&mut self) -> Option<Self::Item> {
            let (ix, adv) = self.offset.advance(1);
            if adv {
                Some(unsafe { self.buffer.get_word(ix) })
            } else {
                None
            }
        }
    }

    impl Parser for ByteParser {
        fn len(&self) -> usize {
            self.offset.lim()
        }

        fn offset(&self) -> usize {
            self.offset.get()
        }

        fn set_fit(&mut self, n: usize) {
            self.offset.set_fit(n)
        }

        fn test_target(&mut self) -> bool {
            self.offset.test_target()
        }

        fn enforce_target(&mut self) {
            self.offset.enforce_target()
        }

        fn consume(&mut self, nbytes: usize) -> ParseResult<&[u8]> {
            let (ix, adv) = self.offset.advance(nbytes);
            if adv {
                Ok(unsafe { self.buffer.get_slice(ix, nbytes) })
            } else {
                Err(ParseError::BufferOverflow {
                    offset: ix,
                    requested: nbytes,
                    buflen: self.buffer.len(),
                })
            }
        }
    }

    pub trait ToParser {
        fn to_parser(self) -> ByteParser;
    }

    impl ToParser for ByteParser {
        fn to_parser(self) -> Self {
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
