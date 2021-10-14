use crate::parse::{byteparser::ToParser, hexstring::HexString};

pub trait Encode<U> {
    fn encode(&self) -> U;
}

pub trait Decode {
    fn decode<U: ToParser>(inp: U) -> Self;
}

impl<T> Encode<HexString> for T
where
    T: Encode<Vec<u8>>
{
    fn encode(&self) -> HexString {
        let bytes : Vec<u8> = self.encode();
        HexString::from(bytes)
    }
}

impl<T> Encode<String> for T
where
    T: Encode<Vec<u8>>,
{
    fn encode(&self) -> String {
        let bytes: Vec<u8> = self.encode();
        unsafe { String::from_utf8_unchecked(bytes) }
    }
}

impl<T> Encode<Vec<u8>> for Option<T>
where
    T: Encode<Vec<u8>>
{
    fn encode(&self) -> Vec<u8> {
        match self {
            Some(val) => val.encode(),
            None => vec![0x00],
        }
    }
}

impl<T: Decode> Decode for Option<T>
{
    fn decode<U: ToParser>(inp: U) -> Self {
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
