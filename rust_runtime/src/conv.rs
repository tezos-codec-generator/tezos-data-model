use crate::builder::{Builder, TransientBuilder};
use crate::parse::byteparser::{Parser, ToParser};

pub mod len;

pub trait Encode {
    fn write(&self, buf: &mut Vec<u8>);

    fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.write(&mut buf);
        buf
    }

    fn encode<U: Builder>(&self) -> U {
        self.to_bytes().into()
    }
}

pub trait EncodeLength: Encode {
    fn enc_len(&self) -> usize {
        self.to_bytes().len()
    }

    fn lazy_encode<'a, U: TransientBuilder<'a>>(&'a self) -> U {
        U::delayed(move |buf| self.write(buf), self.enc_len())
    }
}

impl<T: Encode + len::Estimable + ?Sized> EncodeLength for T {
    fn enc_len(&self) -> usize {
        self.len()
    }
}

pub trait Decode {
    fn parse<P: Parser>(p: &mut P) -> Self;

    fn decode<U: ToParser>(inp: U) -> Self
    where
        Self: Sized,
    {
        let mut p = inp.to_parser();
        Self::parse(&mut p)
    }
}

impl Encode for Vec<u8> {
    fn write(&self, buf: &mut Vec<u8>) {
        buf.extend(self)
    }
}

impl Decode for Vec<u8> {
    fn parse<P: Parser>(p: &mut P) -> Self {
        p.get_dynamic(p.len() - p.offset())
            .expect("<Vec<u8> as Decode>::parse: Buffer read error encountered")
    }
}

impl Encode for &str {
    fn write(&self, buf: &mut Vec<u8>) {
        buf.extend(self.bytes())
    }
}

impl Encode for String {
    fn write(&self, buf: &mut Vec<u8>) {
        buf.extend(self.bytes())
    }
}

impl Decode for String {
    fn parse<P: Parser>(p: &mut P) -> Self {
        let buf: Vec<u8> = p
            .get_dynamic(p.len() - p.offset())
            .expect("<String as Decode>::parse: Buffer read error encountered");
        String::from_utf8(buf)
            .expect("<String as Decode>::parse: UTF-8 conversion error encountered")
    }
}

impl<T: Encode> Encode for Option<T> {
    fn write(&self, buf: &mut Vec<u8>) {
        match self {
            Some(val) => {
                buf.push(0xff);
                val.write(buf);
            }
            None => {
                buf.push(0x00);
            }
        }
    }
}

impl<T: Decode> Decode for Option<T> {
    fn parse<P: Parser>(p: &mut P) -> Self {
        if p.get_bool()
            .expect("Derived Decode::decode for Option<…> encountered error reading leading byte")
        {
            Some(T::parse(p))
        } else {
            None
        }
    }
}


#[cfg(test)]
mod test {
    use crate::{Builder, LazyBuilder};

    use super::EncodeLength;

    #[test]
    fn check() {
        assert_eq!("foo".lazy_encode::<LazyBuilder>().finalize().into_bin().unwrap(), "foo");
    }
}