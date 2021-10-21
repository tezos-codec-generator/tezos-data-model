use crate::parse::{byteparser::ToParser};
use crate::builder::Builder;

pub trait Encode {
    fn encode<U: Builder>(&self) -> U;
}

pub trait Decode {
    fn decode(inp: impl ToParser) -> Self;
}

impl<T: Encode> Encode for Option<T>
{
    fn encode<U: Builder>(&self) -> U {
        match self {
            Some(val) => val.encode(),
            None => U::word(0x00),
        }
    }
}

impl<T: Decode> Decode for Option<T>
{
    fn decode(inp: impl ToParser) -> Self {
        let p = inp.to_parser();
        if p.get_bool()
            .expect("Derived Decode::decode for Option<…> encountered error reading leading byte")
        {
            Some(T::decode(p))
        } else {
            None
        }
    }
}
