mod byteparser;
mod integral;
mod conv;

pub use crate::byteparser::ByteParser;
pub use crate::conv::{ToBinary, FromBinary, Encode, Decode};

fn check(hex_val : (&str, u8)) -> () {
    assert_eq!(u8::bin_decode(hex_val.0), hex_val.1);
    assert_eq!(u8::bin_encode(&(hex_val.1)), hex_val.0);
    assert_eq!(u8::bin_decode(&u8::bin_encode(&hex_val.1)), hex_val.1);
    assert_eq!(u8::bin_encode(&u8::bin_decode(&hex_val.0)), hex_val.0);
}

fn main() {
    let ff = ("ff", 0xffu8);
    let fourtwo = ("42", 0x42u8);

    check(ff);
    check(fourtwo);
}
