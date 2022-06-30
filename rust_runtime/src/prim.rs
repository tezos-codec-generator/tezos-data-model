use crate::conv::{target::Target, Decode, Encode};
use crate::parse::{memoparser::MemoParser, ParseResult, Parser, TryIntoParser};

impl Encode for () {
    fn write_to<U: Target>(&self, _: &mut U) -> usize {
        0
    }

    #[inline(always)]
    fn write_to_vec(&self, _: &mut Vec<u8>) {}

    fn encode<U: Target>(&self) -> U {
        U::create()
    }

    #[inline(always)]
    fn to_bytes(&self) -> Vec<u8> {
        Vec::new()
    }
}

impl Decode for () {
    #[inline]
    fn parse<P: Parser>(_: &mut P) -> ParseResult<()> {
        Ok(())
    }

    fn try_decode<U, P>(_inp: U) -> crate::conv::error::DecodeResult<()>
    where
        Self: Sized,
        P: Parser,
        U: TryIntoParser<P>,
        crate::conv::error::DecodeError: From<U::Error>,
    {
        #[cfg(feature = "check_complete_parse")]
        {
            let p: P = _inp.try_into_parser()?;
            match p.cleanup() {
                Ok(res) => {
                    if res.is_empty() {
                        Ok(())
                    } else {
                        Err(crate::conv::error::DecodeError::NonEmpty(res))
                    }
                }
                Err(inv) => Err(crate::conv::error::DecodeError::Invariant(inv)),
            }
        }
        #[cfg(not(feature = "check_complete_parse"))]
        Ok(())
    }

    fn decode_memo<U>(inp: U) -> Self
    where
        Self: Sized,
        U: TryIntoParser<MemoParser>,
        crate::conv::error::DecodeError: From<U::Error>,
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
        U: TryIntoParser,
        crate::conv::error::DecodeError: From<U::Error>,
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
