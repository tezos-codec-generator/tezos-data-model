use crate::conv::error::{DecodeError, DecodeResult};
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

    cfg_if::cfg_if! {
        if #[cfg(feature = "check_complete_parse")] {
            fn try_decode<U, P>(inp: U) -> DecodeResult<()>
            where
                P: Parser,
                U: TryIntoParser<P>,
                DecodeError: From<U::Error>,
            {
                let p: P = inp.try_into_parser()?;
                match p.cleanup() {
                    Ok(res) => {
                        if res.is_empty() {
                            Ok(())
                        } else {
                            Err(DecodeError::NonEmpty(res))
                        }
                    }
                    Err(inv) => Err(DecodeError::Invariant(inv)),
                }
            }

            fn decode_memo<U>(inp: U) -> Self
            where
                U: TryIntoParser<MemoParser>,
                DecodeError: From<U::Error>,
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
                U: TryIntoParser,
                DecodeError: From<U::Error>,
            {
                Self::try_decode(inp).unwrap_or_else(|err| {
                    panic!(
                        "<{} as Decode>::decode encountered error: {:?}",
                        std::any::type_name::<Self>(),
                        err
                    )
                })
            }
        } else {
            fn try_decode<U, P>(_inp: U) -> DecodeResult<()>
            where
                P: Parser,
                U: TryIntoParser<P>,
                DecodeError: From<U::Error> { Ok(()) }

            fn decode_memo<U>(_inp: U) -> Self
            where
                U: TryIntoParser<MemoParser>,
                DecodeError: From<U::Error>,
            { () }

            fn decode<U>(_inp: U) -> Self
            where
                U: TryIntoParser,
                DecodeError: From<U::Error>,
            { () }
        }
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
