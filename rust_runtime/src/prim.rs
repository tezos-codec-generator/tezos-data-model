use crate::conv::target::Target;
use crate::conv::{Decode, Encode};
use crate::parse::byteparser::ParseResult;
use crate::Parser;

impl Encode for () {
    fn write_to<U: Target>(&self, _: &mut U) -> usize {
        0
    }
}

impl Decode for () {
    fn parse<P: Parser>(_: &mut P) -> ParseResult<Self> {
        Ok(())
    }
}

impl Encode for bool {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        buf.push_one(match self {
            &true => 0xff,
            &false => 0x00,
        })
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
