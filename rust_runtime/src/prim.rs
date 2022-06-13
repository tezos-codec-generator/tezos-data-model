use crate::conv::target::Target;
use crate::conv::{Decode, Encode};
use crate::parse::ParseResult;
use crate::Parser;

impl Encode for () {
    fn write_to<U: Target>(&self, _: &mut U) -> usize {
        0
    }

    #[inline(always)]
    fn write_to_vec(&self, _: &mut Vec<u8>) {}

    fn encode<U: Target>(&self) -> U {
        U::create()
    }

    fn to_bytes(&self) -> Vec<u8> {
        Vec::new()
    }
}

impl Decode for () {
    fn parse<P: Parser>(_: &mut P) -> ParseResult<()> {
        Ok(())
    }

    #[cfg(not(feature = "check_parser_on_drop"))]
    fn try_decode<U, P>(_: U) -> ParseResult<()>
    where
        Self: Sized,
        P: Parser,
        U: crate::TryIntoParser<P>,
    {
        Ok(())
    }

    #[cfg(feature = "check_parser_on_drop")]
    fn try_decode<U, P>(inp: U) -> ParseResult<()>
    where
        Self: Sized,
        P: Parser,
        U: crate::parse::TryIntoParser<P>,
    {
        inp.into_parser()?
    }

    fn decode_memo<U>(inp: U) -> Self
    where
        Self: Sized,
        U: crate::TryIntoParser<crate::parse::memoparser::MemoParser>,
    {
        Self::try_decode(inp).unwrap_or_else(|_| {
            panic!(
                "<{} as Decode>::decode_memo: unable to parse value (ParseError encountered)",
                std::any::type_name::<Self>()
            )
        })
    }

    fn decode<U>(inp: U) -> Self
    where
        Self: Sized,
        U: crate::TryIntoParser,
    {
        Self::try_decode(inp).unwrap_or_else(|err| {
            panic!(
                "<{} as Decode>::decode encountered error: {:?}",
                std::any::type_name::<Self>(),
                err
            )
        })
    }
}

impl Encode for bool {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        buf.push_one(match *self {
            true => 0xff,
            false => 0x00,
        }) + crate::resolve_zero!(buf)
    }
}

impl Decode for bool {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        p.take_bool()
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
