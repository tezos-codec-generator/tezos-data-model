use crate::{Estimable, FixedLength, Parser, conv::{Decode, Encode, EncodeLength}, u30};
use std::{convert::{TryFrom, TryInto}, fmt::{Debug, Display}, marker::PhantomData};

pub struct Dynamic<S, T> {
    contents: T,
    _phantom: std::marker::PhantomData<S>,
}

impl<S: FixedLength, T: Estimable> Estimable for Dynamic<S, T> {
    const KNOWN: Option<usize> = {
        const fn f(x: Option<usize>, y: Option<usize>) -> Option<usize> {
            match (x, y) {
                (Some(m), Some(n)) => Some(m+n),
                _ => None,
            }
        }
        f(S::KNOWN, T::KNOWN)
    };

    fn unknown(&self) -> usize {
        <S as FixedLength>::LEN + self.contents.len()
    }
}

impl<S, T: Debug + crate::conv::len::Estimable> Debug for Dynamic<S, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{} bytes|{:?}]", self.contents.len(), self.contents)
    }
}

impl<S, T: Display> Display for Dynamic<S, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.contents, f)
    }
}


pub trait LenPref
where
    Self: Into<usize> + TryFrom<usize> + Copy + EncodeLength + Decode,
{
}

impl LenPref for u8 {}
impl LenPref for u16 {}
impl LenPref for u30 {}

impl<S: LenPref, T: EncodeLength> Encode for Dynamic<S, T> {
    fn write(&self, buf: &mut Vec<u8>) {
        let l : usize = self.contents.enc_len();
        if let Ok(lp) = l.try_into() {
            buf.reserve(l + <S as EncodeLength>::enc_len(&lp));
            lp.write(buf);
            self.contents.write(buf);
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
