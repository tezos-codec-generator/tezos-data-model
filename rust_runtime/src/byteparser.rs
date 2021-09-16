use std::fmt;
use std::num::ParseIntError;

#[derive(Debug, Clone)]
pub enum InternalErrorKind {
    ConsumeLengthMismatch { expected: usize, actual: usize },
}

impl InternalErrorKind {
    fn length_mismatch(expected: usize, actual: usize) -> Self {
        Self::ConsumeLengthMismatch { expected, actual }
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

impl ParseError {
    fn internal(kind: InternalErrorKind) -> Self {
        Self::InternalError(kind)
    }
}

impl fmt::Display for InternalErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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

struct Bytes(Vec<u8>);

fn to_word(hex_pair: &str) -> Result<u8, ParseIntError> {
    assert_eq!(hex_pair.len(), 2);
    u8::from_str_radix(hex_pair, 16)
}

impl Bytes {
    fn from(s: &str) -> Result<Self, String> {
        let parity = s.len() % 2;

        if parity == 1 {
            Err(format!("Bytes::from: parity of '{}' is odd, not even", s))
        } else {
            let words = (0..s.len())
                .step_by(2)
                .map(|wix| to_word(&s[wix..wix + 2]))
                .collect();
            match words {
                Ok(v) => return Ok(Bytes(v)),
                Err(e) => return Err(format!("Bytes::from: to_word failed with context {:?}", e)),
            }
        }
    }

    unsafe fn get_slice(&self, ix: usize, len: usize) -> &[u8] {
        &self.0[ix..ix + len]
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

pub struct ByteParser {
    _buf: Bytes,
    _offset: std::cell::Cell<usize>,
}

impl ByteParser {
    pub fn parse(s: &str) -> Result<Self, String> {
        match Bytes::from(s) {
            Ok(_buf) => Ok(ByteParser {
                _buf,
                _offset: std::cell::Cell::new(0usize),
            }),
            Err(e) => Err(e),
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
                other => {
                    Err(ParseError::internal(InternalErrorKind::length_mismatch(1, other.len())))
                }
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
                other => {
                    Err(ParseError::internal(InternalErrorKind::length_mismatch(1, other.len())))
                }
            },
            Err(e) => Err(e),
        }
    }
}