use crate::{Builder, Parser, conv::{Decode, Encode}, u30};
use std::{
    convert::{TryFrom, TryInto},
    marker::PhantomData,
};

pub struct Dynamic<S, T> {
    contents: T,
    _phantom: std::marker::PhantomData<S>,
}

trait LenPref
where
    Self: Into<usize> + TryFrom<usize> + Copy + Encode + Decode,
{
}

impl LenPref for u8 {}
impl LenPref for u16 {}
impl LenPref for u30 {}



impl<T: Encode> Encode for Dynamic<u8, T> {
    fn encode<U: Builder>(&self) -> U {
        let payload = Encode::encode::<U>(&self.contents);
        let l = payload.len();

        if let Ok(lp) = l.try_into() {
            u8::encode::<U>(&lp) + payload
        } else {
            panic!(
                "Dynamic<u8, _>: Length prefix {} does not fit into u8 range",
                l
            );
        }
    }
}

impl<T: Decode> Decode for Dynamic<u8, T> {
    fn parse<P: Parser>(p: &mut P) -> Self {
        let buflen = p
            .get_u8()
            .expect("Decode dynamic: could not read 1-byte prefix");
        p.set_fit(buflen as usize);
        let contents = T::parse(p);
        p.enforce_target();
        Dynamic {
            contents,
            _phantom: PhantomData,
        }
    }
}
