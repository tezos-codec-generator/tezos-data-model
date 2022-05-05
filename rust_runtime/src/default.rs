#[macro_export]
macro_rules! dft {
    (@memo create $id:ident : $t:ty = $x:expr) => {
        $crate::lazy_static! {
            pub static ref $id : $t = <$t as $crate::Decode>::decode($crate::hex!($x));
        }
    };
    ($id:ident [$tmp:ident] ($t:ty = $dft:expr)) => {
        #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
        pub struct $id($t);

        dft!(@memo create $tmp : $t = $dft);

        impl ::std::default::Default for $id {
            fn default() -> Self {
                Self($tmp.clone())
            }
        }

        impl From<Option<$t>> for $id {
            fn from(val: Option<$t>) -> $id {
                match val {
                    Some(x) => Self(x),
                    None => Self::default(),
                }
            }
        }

        impl $crate::Encode for $id {
            fn write(&self, buf: &mut Vec<u8>) {
                match &self.0 {
                    x if *x == *$tmp => <Option<$t> as $crate::Encode>::write(&None, buf),
                    x => {
                        buf.push(0xffu8);
                        <$t as $crate::Encode>::write(x, buf);
                    }
                }
            }
        }

        impl $crate::Decode for $id {
            fn parse<P: $crate::Parser>(p: &mut P) -> $crate::ParseResult<Self> {
                Ok(<Option<$t> as $crate::Decode>::parse(p)?.into())
            }
        }

        impl $crate::Estimable for $id {
            const KNOWN : Option<usize> = None;

            fn unknown(&self) -> usize {
                match &self.0 {
                    x if *x == *$tmp => <Option<$t> as $crate::Estimable>::estimate(&None),
                    x => 1 + <$t as $crate::Estimable>::estimate(x),
                }
            }
        }
    };
}