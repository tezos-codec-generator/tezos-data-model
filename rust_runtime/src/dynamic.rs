use crate::{Builder, Parser, conv::{Decode, Encode}, u30};
use std::{
    convert::{TryFrom, TryInto},
    marker::PhantomData,
};

pub struct Dynamic<S, T> {
    contents: T,
    _phantom: std::marker::PhantomData<S>,
}

pub trait LenPref
where
    Self: Into<usize> + TryFrom<usize> + Copy + Encode + Decode,
{
}

impl LenPref for u8 {}
impl LenPref for u16 {}
impl LenPref for u30 {}



impl<S: LenPref, T: Encode> Encode for Dynamic<S, T> {
    fn encode<U: Builder>(&self) -> U {
        let payload = Encode::encode::<U>(&self.contents);
        let l = payload.len();

        if let Ok(lp) = l.try_into() {
            S::encode::<U>(&lp) + payload
        } else {
            panic!(
                "Dynamic<{}, _>: Length prefix {} exceeds bounds of associated type",
                std::any::type_name::<S>(),
                l
            );
        }
    }
}

impl<S: LenPref, T: Decode> Decode for Dynamic<S, T> {
    fn parse<P: Parser>(p: &mut P) -> Self {
        let buflen = S::parse(p);
        p.set_fit(buflen.into());
        let contents = T::parse(p);
        p.enforce_target();
        Dynamic {
            contents,
            _phantom: PhantomData,
        }
    }
}
