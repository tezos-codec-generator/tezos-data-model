#[macro_export]
macro_rules! cstyle {
    ( $name:ident, $backer:ident, { $( $vname:ident = $vdisc:expr ),+ } ) => {
        #[derive(Debug)]
        #[repr($backer)]
        pub enum $name {
            $( $vname = $vdisc ),+
        }

        impl $crate::Decode for $name {
            fn parse<P: $crate::Parser>(p: &mut P) -> $crate::ParseResult<$name> {
                match p.get_tagword::<$name, $backer>(&vec![ $($vdisc as $backer),+ ])? {
                    $(
                        $vdisc => Ok($name::$vname),
                    )+
                    _ => unreachable!(),
                }
            }
        }

        impl $crate::Encode for $name {
            fn write(&self, buf: &mut Vec<u8>) {
                let tag : $backer = match self {
                    $(
                        $name::$vname => $vdisc
                    ),+
                };

                tag.write(buf);
            }
        }

        impl $crate::FixedLength for $name {
            const LEN : usize = <$backer>::LEN;
        }
    }
}

#[macro_export]
macro_rules! structify {
    ( $m:meta, $tname:ident, ) => {
        #[$m]
        pub struct $tname;
    };
    ( $m:meta, $tname:ident, ( $( $v:vis $i:ty ),* )) => {
        #[$m]
        pub struct $tname( $( $v $i),* );
    };
    ( $m:meta, $tname:ident, { $( $v:vis $x:ident : $y:ty ),* }) => {
        #[$m]
        pub struct $tname { $( $v $x : $y ),* } }
}

#[macro_export]
macro_rules! data {
    { $name:ident, $backer:ident, { $( $disc:expr => $vname:ident $($vspec:tt)? ),+ } } => {
        pub mod subtypes {
            #![allow(non_camel_case_types)]
            use super::*;
            use $crate::FixedLength;
            $(
                $crate::structify!(derive(Encode,Decode,Estimable,Debug), $vname, $($vspec)?);
            )+
        }


        #[derive(Debug)]
        pub enum $name {
            $( $vname(subtypes::$vname) ),+
        }

        impl $crate::Decode for $name {
            fn parse<P: $crate::Parser>(p: &mut P) -> $crate::ParseResult<$name> {
                match p.get_tagword::<$name, $backer>(&vec![ $( $disc as $backer ),+ ])? {
                    $(
                        $disc => {
                            Ok($name::$vname(<subtypes::$vname>::parse(p)?))
                        }
                    )+
                    _ => unreachable!(),
                }
            }
        }

        impl $crate::Encode for $name {
            fn write(&self, buf: &mut Vec<u8>) {
                match self {
                    $(
                        $name::$vname(inner) => {
                            <$backer>::write(&$disc, buf);
                            <subtypes::$vname>::write(inner, buf);
                        }
                    )+
                };
            }
        }

        impl $crate::Estimable for $name {
            const KNOWN : Option<usize> = None;

            fn unknown(&self) -> usize {
                match self {
                    $(
                        $name::$vname(inner) =>
                            <$backer as FixedLength>::LEN + <subtypes::$vname as Estimable>::len(inner)
                    ),+
                }
            }
        }
    }
}
