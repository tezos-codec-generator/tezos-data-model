use crate::conv::{Decode, Encode};
use crate::parse::byteparser::ParseResult;
use crate::{Parser};

impl Encode for () {
    fn write(&self, _: &mut Vec<u8>) {}
}

impl Decode for () {
    fn parse<P: Parser>(_: &mut P) -> ParseResult<Self> {
        Ok(())
    }
}

impl Encode for bool {
    fn write(&self, buf: &mut Vec<u8>) {
        match self {
            &true => buf.push(0xff),
            &false => buf.push(0x00),
        }
    }
}

impl Decode for bool {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        p.get_bool()
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    #[test]
    fn unit_test() {
        assert_eq!((), <()>::decode(""));
    }
}