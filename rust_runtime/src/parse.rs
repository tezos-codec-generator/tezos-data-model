pub mod errors {
    use std::{fmt::*, string::FromUtf8Error};

    use crate::bound::OutOfRange;

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
    pub enum ExternalErrorKind {
        UncoercableString(FromUtf8Error),
        IntRangeViolation(OutOfRange<i64>),
        FloatRangeViolation(OutOfRange<f64>),
    }

    impl Display for ExternalErrorKind {
        fn fmt(&self, f: &mut Formatter) -> Result {
            match self {
                ExternalErrorKind::UncoercableString(err) => {
                    write!(
                        f,
                        "parsed byte-array could not be coerced to String: {}",
                        err
                    )
                }
                ExternalErrorKind::IntRangeViolation(x) => {
                    write!(f, "{}", x)
                }
                ExternalErrorKind::FloatRangeViolation(x) => {
                    write!(f, "{}", x)
                }
            }
        }
    }

    #[derive(Debug, Clone)]
    pub enum ParseError {
        InternalError(InternalErrorKind),
        ExternalError(ExternalErrorKind),
        BufferOverflow {
            buflen: usize,
            offset: usize,
            requested: usize,
        },
        InvalidBoolean(u8),
        InvalidTagWord {
            expected: Vec<u8>,
            for_type: String,
            actual: u8,
        },
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
                }
                ParseError::InternalError(err) => {
                    write!(f, "internal error ({})", err)
                }
                ParseError::ExternalError(err) => {
                    write!(f, "external error ({})", err)
                }
                ParseError::InvalidBoolean(byte) => {
                    write!(f, "expected boolean := (0xff | 0x00), got 0x{:02x}", byte)
                }
                ParseError::InvalidTagWord {
                    expected,
                    for_type,
                    actual,
                } => {
                    write!(
                        f,
                        "discriminant for type {} must be one of `0x{:02x?}`, got 0x{:02x}",
                        for_type, expected, actual
                    )
                }
                ParseError::NonTerminating(buf) => {
                    write!(f, "self-terminating codec cut off (end-of-window encountered before terminating condition met): `{}`", crate::util::hex_of_bytes(buf))
                }
            }
        }
    }

    impl From<FromUtf8Error> for ParseError {
        fn from(err: FromUtf8Error) -> Self {
            Self::ExternalError(ExternalErrorKind::UncoercableString(err))
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

    impl std::ops::AddAssign<HexString> for HexString {
        fn add_assign(&mut self, mut rhs: HexString) {
            self.words.append(&mut rhs.words)
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

    impl Into<Vec<u8>> for HexString {
        fn into(self) -> Vec<u8> {
            self.words
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
            <$crate::parse::hexstring::HexString as std::convert::TryFrom<&str>>::try_from($s)
                .expect("hex! macro encountered error")
        };
    }

    impl Builder for HexString {
        type Segment = Vec<u8>;
        type Final = Self;

        fn promote(seg: Self::Segment) -> Self {
            Self { words: seg }
        }

        fn word(b: u8) -> Self {
            Self { words: vec![b] }
        }

        fn words<const N: usize>(b: [u8; N]) -> Self {
            Self { words: b.to_vec() }
        }

        fn finalize(self) -> Self {
            self
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

    /**
     # Parser

      This trait is an abstraction over types respresenting a stateful
      parse-object, with default implementations for a variety of monomorphic
      `get_*` functions, as well as query operations on the internal state,
      and state-mutational functions that operate on *context-windows*.

     ## Model

     While the implementing types are largely free to define their own
     operational semantics for the required methods of this function, the
     intensional semantics are as follows:

     * The Parser-object is constructed over an immutable byte-buffer.
     * All parsing is done in a non-backtracking, zero-lookahead fashion; a byte in the buffer
       can only be viewed by consuming it, and only after all preceding indices in the buffer
       have been consumed; after a byte is consumed, it cannot be consumed again.
     * A *context-window*, or a bounded contiguous view of a section of the buffer,
       may be constructed. While a context-window exists, any bytes beyond its upper bound
       are protected and cannot be consumed by any Parser method until that
       context window is lifted. A context-window can only be lifted by calling
       [enforce_target] when all bytes within the window have been consumed.

    ## Context-Windows

    In order to facilitate bounds-setting and bounds-checking for dynamically sized elements with length prefixes,
    `Parser` uses a model of *context windows*, which are conceptually (though not necessarily implementationally) a stack
    of target offsets, which may in fact be hard lower bounds on remainding-buffer-length in the case of slice-based parsers, or fixed values
    of the mutating parse-head for buffer-based implementations such as [ByteParser].

    The following properties should be respected by each implementation of the `Parser` trait:

    * A fresh `p : impl Parser` object should have `p.offset() == 0` and `p.len()` equal to the length of the parse-buffer
    * `self.len() - self.offset()` is the largest possible `n` for which `self.consume(n)` returns an `Ok(_)` value, which should also be the largest possible `n` for which `self.set_fit(n)` succeeds. Both should fail for any greater values of `n`, either through `Err(_)` returns or panics.
    * The value of `self.len() - self.offset()` before and after a call to `self.consume(n)` should represent a decrease by `n` if the consume call is an `Ok(_)` value, or remain unchanged if it is an `Err(_)` value. Only one of `self.len()` and `self.offset()` should change in this fashion.
    * `self.set_fit(m)` should fail whenever `self.len() < m + self.offset()`, and succeed otherwise
    * Immediately after a successful call of `self.set_fit(n)`, `self.len() == n + self.offset()` should hold.
    * `self.test_target()` should return `true` if and only if `self.offset() == self.len()` holds with at least one context window present
    * `self.enforce_target()` should remove the most recently set target if `self.test_target()` would return true, and panic otherwise

    */
    pub trait Parser: Iterator<Item = u8> {
        /** Computes the length of the current view of the Parser's buffer.
         *
         * Decrements in the shrinking-slice model, and remains invariant modulo context-window
         * manipulation in the buffer-with-offset model
         */
        fn len(&self) -> usize;

        /** Computes the current value of the offset into the Parser's buffer.
         *
         * This should either be invariant, or increase by the number of bytes consumed
         * by any method that returns bytes from the buffer.
         */
        fn offset(&self) -> usize;

        fn remainder(&self) -> usize {
            self.len() - self.offset()
        }

        /** Consumes the speficied number of bytes from buffer[nbytes]
         */
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

        fn get_tagword<T>(&mut self, valid: &[u8]) -> ParseResult<u8> {
            match self.next() {
                Some(byte) => {
                    if valid.contains(&byte) {
                        Ok(byte)
                    } else {
                        Err(ParseError::InvalidTagWord {
                            expected: valid.to_vec(),
                            actual: byte,
                            for_type: std::any::type_name::<T>().to_owned(),
                        })
                    }
                }
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
            F: Fn(u8) -> bool,
        {
            let mut ret: Vec<u8> = Vec::with_capacity(self.len() - self.offset());
            loop {
                if let Some(byte) = self.next() {
                    ret.push(byte);
                    if is_terminal(byte) {
                        break Ok(ret);
                    }
                } else {
                    break Err(ParseError::NonTerminating(ret));
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
