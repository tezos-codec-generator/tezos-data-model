use crate::builder::{Builder, TransientBuilder};
use crate::parse::byteparser::{Parser, ToParser, ParseResult};

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

    fn lazy_encode<'a, U>(&'a self) -> U where U: TransientBuilder<'a> + 'a {
        U::delayed(move |buf| Encode::write(self, buf), self.enc_len())
    }
}

impl<T: Encode + len::Estimable + ?Sized> EncodeLength for T {
    fn enc_len(&self) -> usize {
        self.len()
    }
}

pub trait Decode {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self>
    where Self: Sized;

    fn decode<U: ToParser>(inp: U) -> Self
    where
        Self: Sized,
    {
        let mut p = inp.to_parser();
        Self::parse(&mut p).expect(&format!("<{} as Decode>::decode: unable to parse value (ParseError encountered): ", std::any::type_name::<Self>()))
    }
}

impl Encode for Vec<u8> {
    fn write(&self, buf: &mut Vec<u8>) {
        buf.extend(self)
    }
}

impl Decode for Vec<u8> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        p.get_dynamic(p.len() - p.offset())
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
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let buf: Vec<u8> = p.get_dynamic(p.len() - p.offset())?;

        Ok(String::from_utf8(buf)?)
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
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        match p.get_tagword::<Option<T>, u8>(&[0x00, 0xff])? {
            0xff => Ok(Some(T::parse(p)?)),
            0x00 => Ok(None),
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{Builder, LazyBuilder};

    use super::EncodeLength;

    #[test]
    fn check() {
        assert_eq!(
            "foo"
                .lazy_encode::<LazyBuilder>()
                .finalize()
                .into_bin()
                .unwrap(),
            "foo"
        );
    }
}
