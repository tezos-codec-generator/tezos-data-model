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

        pub unsafe fn get_word(&self, ix: usize) -> &u8 {
            &self.0[ix]
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }
    }
}

pub mod byteparser {
    use super::bytes::Bytes;
    use super::errors::ParseError;
    use std::cell::Cell;
    use std::convert::TryFrom;

    pub struct ByteParser {
        _buf: Bytes,
        _offset: Cell<usize>,
    }

    impl ByteParser {
        pub fn parse(input: &str) -> Self {
            match Bytes::try_from(input) {
                Ok(_buf) => Self {
                    _buf,
                    _offset: Cell::new(0usize),
                },
                Err(e) => panic!("error encountered in <…>::ByteParser::parse: {}", e),
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

        pub fn get_uint8(&self) -> Result<u8, ParseError> {
            match self.next() {
                Some(&byte) => Ok(byte),
                None => Err(ParseError::BufferOverflow {
                    buflen: self._buf.len(),
                    requested: 1,
                    offset: self._offset.get(),
                }),
            }
        }

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

        pub fn get_dynamic(&self, nbytes: usize) -> Result<Vec<u8>, ParseError> {
            self.consume(nbytes).map(Vec::from)
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

    impl ToParser for &str {
        fn to_parser(self) -> ByteParser {
            ByteParser::parse(self)
        }
    }

    impl ToParser for String {
        fn to_parser(self) -> ByteParser {
            ByteParser::parse(&self)
        }
    }

}
