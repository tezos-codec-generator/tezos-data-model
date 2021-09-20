use crate::parse::byteparser::{ToParser};

pub trait Encode<U> {
    fn encode(&self) -> U;
}

pub trait Decode {
    fn decode<U: ToParser>(inp: U) -> Self;
}

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
