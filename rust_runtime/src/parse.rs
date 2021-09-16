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

        pub fn len(&self) -> usize {
            self.0.len()
        }
    }
}

pub mod byteparser {
    use super::bytes::Bytes;
    use super::errors::{ConvError, InternalErrorKind, ParseError};
    use core::panic;
    use std::cell::Cell;
    use std::convert::{TryFrom, TryInto};
    use std::fmt::Display;

    pub struct ByteParser {
        _buf: Bytes,
        _offset: Cell<usize>,
    }

    impl TryFrom<&str> for ByteParser {
        type Error = ConvError<String>;

        fn try_from(s: &str) -> Result<Self, Self::Error> {
            match Bytes::try_from(s) {
                Ok(_buf) => Ok(ByteParser {
                    _buf,
                    _offset: Cell::new(0usize),
                }),
                Err(e) => Err(e),
            }
        }
    }

    impl ByteParser {
        pub fn parse<T>(input: T) -> Self
        where
            T: TryInto<Self>,
            T::Error: Display,
        {
            match input.try_into() {
                Ok(p) => p,
                Err(err) => panic!("kernel::parse::byteparser::ByteParser::parse: {}", err),
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

        pub fn get_uint8(&self) -> Result<u8, ParseError> {
            match self.consume(1) {
                Ok(bytes) => match bytes {
                    &[byte] => Ok(byte),
                    other => Err(ParseError::InternalError(
                        InternalErrorKind::ConsumeLengthMismatch {
                            expected: 1,
                            actual: other.len(),
                        },
                    )),
                },
                Err(e) => Err(e),
            }
        }

        pub fn get_bool(&self) -> Result<bool, ParseError> {
            match self.consume(1) {
                Ok(bytes) => match bytes {
                    &[0x00] => Ok(false),
                    &[0xff] => Ok(true),
                    &[byte] => Err(ParseError::InvalidBoolean(byte)),
                    other => Err(ParseError::InternalError(
                        InternalErrorKind::ConsumeLengthMismatch {
                            expected: 1,
                            actual: other.len(),
                        },
                    )),
                },
                Err(e) => Err(e),
            }
        }
    }
}
