mod parse;
mod prim;
mod conv;

pub use crate::parse::byteparser::ByteParser;
pub use crate::conv::{Encode, Decode};

fn check(hex_val : (&str, u8)) -> () {
    assert_eq!(u8::decode(hex_val.0), hex_val.1);
    assert_eq!(u8::encode(&(hex_val.1)), hex_val.0);
    assert_eq!(u8::decode(u8::encode(&hex_val.1)), hex_val.1);
    assert_eq!(u8::encode(&u8::decode(hex_val.0)), hex_val.0);
}

fn main() {
    let ff = ("ff", 0xffu8);
    let fourtwo = ("42", 0x42u8);

    check(ff);
    check(fourtwo);
}
