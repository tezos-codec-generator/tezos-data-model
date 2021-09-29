use std::num::ParseIntError;
use std::fmt;

#[derive(Debug, Clone)]
pub struct BufferOverflow(usize,usize,usize);

impl fmt::Display for BufferOverflow {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "target position at _{}_+<{}> overflows [{}]", self.0, self.1, self.2)
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
                Result::Ok(v) => { return Ok(Bytes(v)) }
                Result::Err(e) => { return Err(format!("Bytes::from: to_word failed with context {:?}", e)) }
            }
        }
    }

    unsafe fn get_slice(&self, ix: usize, len: usize) -> &[u8] {
        &self.0[ix..ix+len]
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}


pub struct ByteParser {
    _buf : Bytes,
    _offset : std::cell::Cell<usize>
}

impl ByteParser {
    pub fn parse(s: &str) -> Result<Self, String> {
        match Bytes::from(s) {
            Result::Ok(_buf) => {
                Ok(ByteParser {
                    _buf,
                    _offset: std::cell::Cell::new(0usize),
                })
            }
            Result::Err(e) => {
                Err(e)
            }
        }
    }

    fn consume(&self, nbytes: usize) -> Result<&[u8],BufferOverflow> {
        let cur : usize = self._offset.get();

        let tgt = cur + nbytes;

        if cur + nbytes > self._buf.len() {
            Err(BufferOverflow(cur, nbytes, self._buf.len()))
        } else {
            Ok(
                unsafe {
                    let ret = self._buf.get_slice(cur, nbytes);
                    self._offset.set(tgt);
                    ret
                })
        }
    }

    pub fn get_uint8(&self) -> Result<u8, BufferOverflow> {
        match self.consume(1) {
            Result::Ok(ws) => {
                assert_eq!(ws.len(), 1);
                Ok(ws[0])
            }
            Result::Err(e) => {
                Err(e) 
            }
        }
    }
}