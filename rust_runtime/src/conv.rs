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