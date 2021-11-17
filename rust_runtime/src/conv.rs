use crate::builder::Builder;
use crate::parse::byteparser::{Parser, ToParser};

pub mod len {
    pub trait FixedLength {
        const LEN: usize;
    }

    macro_rules! fix_length {
        ($n:expr, $($x:ty),+) => {
            $(impl FixedLength for $x {
                const LEN : usize = $n;
            })+
        };
    }

    fix_length!(0, ());
    fix_length!(1, u8, i8, bool);
    fix_length!(2, u16, i16);
    fix_length!(4, u32, i32);
    fix_length!(8, u64);

    impl<T: FixedLength, const N: usize> FixedLength for [T; N] {
        const LEN: usize = N * T::LEN;
    }

    pub trait ScalarLength {
        const FIXED: Option<usize> = None;

        type Elem: FixedLength;

        const PER_ELEM: usize = <Self::Elem as FixedLength>::LEN;

        fn n_elems(&self) -> usize;
    }

    impl<T: FixedLength> ScalarLength for T {
        const FIXED: Option<usize> = Some(T::LEN);

        type Elem = Self;

        fn n_elems(&self) -> usize {
            1
        }
    }

    pub trait Estimable {
        const KNOWN: Option<usize>;

        fn unknown(&self) -> usize;

        fn len(&self) -> usize {
            Self::KNOWN.unwrap_or_else(|| self.unknown())
        }
    }

    impl<T> Estimable for T
    where
        T: ScalarLength,
    {
        const KNOWN: Option<usize> = Self::FIXED;

        fn unknown(&self) -> usize {
            self.n_elems() * Self::PER_ELEM
        }
    }

    impl<T> Estimable for Option<T>
    where
        T: Estimable,
    {
        const KNOWN: Option<usize> = None;

        fn unknown(&self) -> usize {
            match self {
                &None => 1,
                Some(x) => 1 + x.len(),
            }
        }
    }

    impl<T: FixedLength> ScalarLength for Vec<T> {
        type Elem = T;

        fn n_elems(&self) -> usize {
            self.len()
        }
    }

    impl ScalarLength for String {
        type Elem = u8;
        fn n_elems(&self) -> usize {
            self.len()
        }
    }
}

pub trait Encode {
    fn write(&self, buf: &mut Vec<u8>);

    fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.write(&mut buf);
        buf
    }

    fn encode<U: Builder>(&self) -> U {
        self.to_bytes().into_iter().collect()
    }
}

pub trait EncodeLength: Encode {
    fn enc_len(&self) -> usize {
        self.to_bytes().len()
    }
}

impl<T: Encode + len::Estimable> EncodeLength for T {
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
