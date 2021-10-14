mod parse;
mod prim;
mod conv;
mod int;

pub use crate::parse::byteparser::ByteParser;
pub use crate::conv::{Encode, Decode};

fn check<T>(hex_val : (&str, T)) -> ()
where
T: Encode<String> + Decode + Eq + std::fmt::Debug
{
    assert_eq!(T::decode(hex_val.0), hex_val.1);
    assert_eq!(T::encode(&(hex_val.1)), hex_val.0);
    assert_eq!(T::decode(T::encode(&hex_val.1)), hex_val.1);
    assert_eq!(T::encode(&T::decode(hex_val.0)), hex_val.0);
}

fn main() {
    check(("ff", 0xffu8));
    check(("42", 0x42u8));
}
