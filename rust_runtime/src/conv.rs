use crate::parse::byteparser::{ByteParser, ToParser};

pub trait ToBinary {
    fn bin_encode(&self) -> String;
}

pub trait FromBinary {
    fn bin_decode(inp: &str) -> Self;
}

pub trait Encode<U> {
    fn encode(&self) -> U;
}

pub trait Decode<U> {
    fn decode(inp: U) -> Self;
}

impl<T> ToBinary for Option<T>
where
    T: ToBinary,
{
    fn bin_encode(&self) -> String {
        match &self {
            Some(val) => T::bin_encode(val),
            None => String::from("00"),
        }
    }
}

/*
impl<T> FromBinary for Option<T> where T: FromBinary {
    fn bin_decode(inp: &str) -> Self {
        match crate::byteparser::ByteParser::parse(inp) {
            Ok(p) => {
                match p.get_bool() {
                    Ok(true) => Some(T::bin_decode(&inp[1..])),
                    Ok(false) => None,
                    Err(err) => std::panic!("{}", err),
                }
            },
            Err(err) => std::panic!("{}", err),
        }
    }
}
*/

impl<T> Encode<String> for Option<T>
where
    T: Encode<String>,
{
    fn encode(&self) -> String {
        match self {
            Some(val) => val.encode(),
            None => String::from("00"),
        }
    }
}

impl<T, U> Decode<U> for Option<T>
where
    U: ToParser,
    T: Decode<ByteParser>
{
    fn decode(inp: U) -> Self {
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
