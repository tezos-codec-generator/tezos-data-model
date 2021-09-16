pub trait ToBinary {
    fn bin_encode(&self) -> String;
}

pub trait FromBinary {
    fn bin_decode(inp : &str) -> Self;
}

pub trait Encode<U> {
    fn encode(&self) -> U;
}

pub trait Decode<T> {
    fn decode(&self) -> T;
}

/*
impl<T> ToBinary for Option<T> where T: ToBinary {
    fn bin_encode(&self) -> String {
        match &self {
            Some(val) => T::bin_encode(val),
            None => String::from("00"),
        }
    }
}

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

impl<T> Encode<String> for Option<T> where T: Encode<String> {
    fn encode(&self) -> String { 
        match self {
            Some(val) => val.encode(),
            None => String::from("00"),
        }
    }
}

impl<T, U> Decode<Option<T>> for U where
U: Decode<T> + Decode<bool> {
    fn decode(&self) -> Option<T> {
        if self.decode() {
            // this has not been implemented sufficiently to define
        }
        match crate::byteparser::ByteParser::parse(inp) {
            Ok(p) => {
                match p.get_bool() {
                    Ok(true) => Some(T::bin_decode(&self[1..])),
                    Ok(false) => None,
                    Err(err) => std::panic!("{}", err),
                }
            },
            Err(err) => std::panic!("{}", err),
        }
    }
}
*/