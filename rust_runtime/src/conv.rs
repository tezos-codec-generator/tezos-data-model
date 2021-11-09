use crate::parse::byteparser::{ToParser, Parser};
use crate::builder::Builder;

pub trait Encode {
    fn encode<U: Builder>(&self) -> U;
}

pub trait Decode: Sized {
    fn parse<P: Parser>(p: &mut P) -> Self;

    fn decode<U: ToParser>(inp: U) -> Self {
        let mut p = inp.to_parser();
        Self::parse(&mut p)
    }
}

impl Encode for Vec<u8> {
    fn encode<U: Builder>(&self) -> U {
        self.iter().map(|&byte| byte).collect()
    }
}

impl Decode for Vec<u8> {
    fn parse<P: Parser>(p: &mut P) -> Self {
        p.get_dynamic(p.len() - p.offset()).expect("<Vec<u8> as Decode>::parse: Buffer read error encountered")
    }
}


impl Encode for String {
    fn encode<U: Builder>(&self) -> U {
        self.bytes().collect()
    }
}

impl Decode for String {
    fn parse<P: Parser>(p: &mut P) -> Self {
        let buf: Vec<u8> = p.get_dynamic(p.len() - p.offset()).expect("<String as Decode>::parse: Buffer read error encountered");
        String::from_utf8(buf).expect("<String as Decode>::parse: UTF-8 conversion error encountered")
    }
}


impl<T: Encode> Encode for Option<T>
{
    fn encode<U: Builder>(&self) -> U {
        match self {
            Some(val) => U::word(0xff) + val.encode(),
            None => U::word(0x00),
        }
    }
}

impl<T: Decode> Decode for Option<T>
{
    fn parse<P: Parser>(p: &mut P) -> Self {
        if p.get_bool()
            .expect("Derived Decode::decode for Option<…> encountered error reading leading byte")
        {
            Some(T::parse(p))
        } else {
            None
        }
    }
}
