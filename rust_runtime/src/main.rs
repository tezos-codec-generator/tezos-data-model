mod parse;
mod prim;
mod conv;
mod int;
mod builder;
mod util;

pub use crate::parse::byteparser::ByteParser;
pub use crate::conv::{Encode, Decode};
pub use crate::builder::{Builder, owned::OwnedBuilder};

fn check<T>(hex_val : (&str, T)) -> ()
where
T: Encode + Decode + Eq + std::fmt::Debug
{
    assert_eq!(T::decode(hex_val.0), hex_val.1);
    assert_eq!(T::encode::<OwnedBuilder>(&(hex_val.1)).show_hex(), hex_val.0);
    assert_eq!(T::decode(T::encode::<OwnedBuilder>(&hex_val.1).into_vec()), hex_val.1);
    assert_eq!(T::encode::<OwnedBuilder>(&T::decode(hex_val.0)).show_hex(), hex_val.0);
}

fn main() {
    check(("ff", 0xffu8));
    check(("42", 0x42u8));
}
