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

pub mod bytes {
    use super::errors::ConvError::{HexError, ParityError};
    use std::convert::TryFrom;
    use std::num::ParseIntError;

    pub struct Bytes(Vec<u8>);

    fn to_word(hex_pair: &str) -> Result<u8, ParseIntError> {
        assert_eq!(hex_pair.len(), 2);
        u8::from_str_radix(hex_pair, 16)
    }

    impl From<&[u8]> for Bytes {
        fn from(bytes: &[u8]) -> Self {
            Self(bytes.to_owned())
        }
    }

    impl From<Vec<u8>> for Bytes {
        fn from(bytes: Vec<u8>) -> Self {
            Self(bytes)
        }
    }

    impl<const N: usize> From<[u8; N]> for Bytes {
        fn from(bytes: [u8; N]) -> Self {
            Self(bytes.to_vec())
        }
    }

    impl TryFrom<&str> for Bytes {
        type Error = super::errors::ConvError<String>;

        fn try_from(s: &str) -> Result<Self, Self::Error> {
            let parity = s.len() % 2;

            if parity == 1 {
                Err(ParityError(s.to_owned()))
            } else {
                let words = (0..s.len())
                    .step_by(2)
                    .map(|wix| to_word(&s[wix..wix + 2]))
                    .collect();
                match words {
                    Ok(v) => Ok(Bytes(v)),
                    Err(_) => Err(HexError(s.to_owned())),
                }
            }
        }
    }

    impl Bytes {
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

    use super::bytes::Bytes;
    use super::errors::ParseError;
    use std::cell::Cell;
    use std::convert::{TryFrom, TryInto};
    use std::ops::Deref;

    pub struct ByteParser {
        _buf: Bytes,
        _offset: Cell<usize>,
    }

    impl ByteParser {
        pub fn parse<T>(input: T) -> Self
        where
            Bytes: TryFrom<T>,
            <T as TryInto<Bytes>>::Error: std::fmt::Display,
        {
            match Bytes::try_from(input) {
                Ok(_buf) => Self {
                    _buf,
                    _offset: Cell::new(0usize),
                },
                Err(e) => panic!("ByteParser::parse: error encountered: {}", e),
            }
        }

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

        fn consume(&self, nbytes: usize) -> Result<&[u8], ParseError> {
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
        pub fn get_u8(&self) -> Result<u8, ParseError> {
            match self.next() {
                Some(&byte) => Ok(byte),
                None => Err(ParseError::BufferOverflow {
                    buflen: self._buf.len(),
                    requested: 1,
                    offset: self._offset.get(),
                }),
            }
        }

        pub fn get_i8(&self) -> Result<i8, ParseError> {
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
        fn consume_arr<const N: usize>(&self) -> Result<[u8; N], ParseError> {
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
        pub fn get_u16(&self) -> Result<u16, ParseError> {
            self.consume_arr::<2>().map(u16::from_be_bytes)
        }

        pub fn get_i16(&self) -> Result<i16, ParseError> {
            self.consume_arr::<2>().map(i16::from_be_bytes)
        }

        pub fn get_u32(&self) -> Result<u32, ParseError> {
            self.consume_arr::<4>().map(u32::from_be_bytes)
        }

        pub fn get_i32(&self) -> Result<i32, ParseError> {
            self.consume_arr::<4>().map(i32::from_be_bytes)
        }

        pub fn get_u64(&self) -> Result<u64, ParseError> {
            self.consume_arr::<8>().map(u64::from_be_bytes)
        }

        pub fn get_i64(&self) -> Result<i64, ParseError> {
            self.consume_arr::<8>().map(i64::from_be_bytes)
        }
    }

    impl ByteParser {
        pub fn get_bool(&self) -> Result<bool, ParseError> {
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
        pub fn get_dynamic(&self, nbytes: usize) -> Result<Vec<u8>, ParseError> {
            self.consume(nbytes).map(Vec::from)
        }

        pub fn get_fixed<const N: usize>(&self) -> Result<[u8; N], ParseError> {
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
        Bytes: TryFrom<T>,
        <T as TryInto<Bytes>>::Error : std::fmt::Display,
    {
        fn to_parser(self) -> ByteParser {
            ByteParser::parse(self)
        }
    }

    impl<const N: usize> ToParser for &[u8; N]
    {
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
