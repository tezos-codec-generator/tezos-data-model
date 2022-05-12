use crate::{Estimable, FixedLength, Parser, conv::{Decode, Encode, EncodeLength}, u30, parse::byteparser::ParseResult};
use std::{convert::{TryFrom, TryInto}, fmt::{Debug, Display}, marker::PhantomData};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dynamic<S, T> {
    contents: T,
    _phantom: PhantomData<S>,
}



impl<S, T> Dynamic<S, T> {
    pub fn wrap(contents: T) -> Self {
        Self { contents, _phantom: PhantomData }
    }
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
        <S as FixedLength>::LEN + self.contents.estimate()
    }
}

impl<S, T: Debug + crate::conv::len::Estimable> Debug for Dynamic<S, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{} bytes|{:?}]", self.contents.estimate(), self.contents)
    }
}

impl<S, T: Display> Display for Dynamic<S, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.contents, f)
    }
}

impl<S, T> std::ops::Deref for Dynamic<S, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.contents
    }
}

pub unsafe trait LenPref
where
    Self: Into<usize> + TryFrom<usize> + Copy + EncodeLength + Decode,
{
}

unsafe impl LenPref for u8 {}
unsafe impl LenPref for u16 {}
unsafe impl LenPref for u30 {}

impl<S: LenPref, T: EncodeLength> Encode for Dynamic<S, T> {
    fn write_to<U: crate::conv::target::Target>(&self, buf: &mut U) -> usize {
        let l : usize = self.contents.enc_len();
        if let Ok(lp) = l.try_into() {
            buf.anticipate(l + <S as EncodeLength>::enc_len(&lp));
            lp.write_to(buf) + self.contents.write_to(buf)
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
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let buflen = S::parse(p)?;
        p.set_fit(buflen.into());
        let contents = T::parse(p)?;
        p.enforce_target();
        Ok(Dynamic {
            contents,
            _phantom: PhantomData,
        })
    }
}
