/// Generates a type-definition and associated implementations
/// of the runtime traits [`Encode`](crate::conv::Encode), [`Decode`](crate::conv::Decode), and [`FixedLength`](crate::conv::len::FixedLength)
/// for a C-Style enum (i.e. type-level association between type-scoped identifiers
/// and unique unsigned integral constants, without any associated data).
///
/// # Syntax
///
/// The following syntactical conventions are adopted for the generative macro `cstyle`:
///
/// ```ignore
/// cstyle!( <TYPE_ID> , <REPR := (u8|u16|u32)> , '{' <CONSTR_ID> = <TAG> (, <CONSTR_ID> = <TAG> )* ,? '}')
/// ```
///
/// where `<TYPE_ID>` is a valid and unused (in the current scope) identifier to be used as the
/// name of the enumerated type, `<REPR>` is one of the literals `u8 | u16 | u32` and determines
/// the type used to represent the numerical discriminant in memory and in serialization/deserialization,
/// and each `<CONSTR_ID> = <TAG>` sub-expression corresponds to a unique variant of the enumerated type,
/// with a mandatory explicit non-negative integral constant expression <TAG> (ideally a numeric literal)
/// used as the in-memory representation, and in the codec layer as the binary representation,
/// of the constructor `<CONSTR_ID>`, which should be a unique identifier. A comma must separate each association,
/// but a trailing comma after the final one is optional. At least one constructor must be provided in order
/// for `cstyle` to be syntactically valid, as an empty enum is not semantically sound in the context in which
/// this macro is intended to be used.
///
/// # Examples
///
/// ```
/// use crate::conv::Decode;
///
/// cstyle!(SmallPrime, u8, { Two = 2, Three = 3, Five = 5, Seven = 7 });
/// assert_eq(SmallPrime::Five as u8, 5u8);
/// assert_eq(SmallPrime::decode("05") as u8, SmallPrime::Five as u8);
/// ```
///
/// #
///
/// ```
/// cstyle!(NarrowUnit, u8, { Unit = 0 });
/// cstyle!(WideUnit, u32, { Unit = 0 });
/// assert_eq(std::mem::size_of::<NarrowUnit>(), 1);
/// assert_eq(std::mem::size_of::<WideUnit>(), 4);
/// ```
///
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

/// Helper macro used to produce a syntactically valid standlone `struct` declaration
/// with a mandatory attribute.
///
/// # Syntax
///
/// The syntax of `structify` is as follows:
///
/// ```ignore
/// structify!( <ATTR>, <TYPE_ID>, <STRUCT_STUB> )
/// ```
///
/// which will produce
///
/// ```ignore
/// #[<ATTR>]
/// pub struct <TYPE_ID><STRUCT_STUB><DELIM>
/// ```
///
/// where `<ATTR>` is the contents of an attribute item to attach to the definition,
/// <TYPE_ID> is the name of the struct being defined, and <STRUCT_STUB> is the sequence
/// of tokens that follow the name of a struct type in the conventional declaration syntax,
/// i.e. one of the following:
///   * The absence of any lexical items (denoted as `ε`)
///   * A parenthetical list of comma-separated `<TYPE>` expressions, each with optional preceding visibility qualifiers
///   * A `{}`-wrapped block of comma-separated `<FIELD_ID>: <TYPE>` expressions with optional preceding visibility qualifiers
///
/// The first will generate a unit-like struct declaration (e.g. `pub struct Foo;`) , with `<DELIM> := ';'`
/// The second will generate a tuple-struct declaration (e.g. `pub struct Bar(pub i32, bool);`), with `<DELIM> := ';'`
/// The third will generate a record struct declaration (e.g. `pub struct Baz { pub first: String, second: Option<Box<Baz>> }`), with `<DELIM> := ε`
///
/// # Usage
///
/// This macro is not meant to be manually invoked, but is exported so that it may be called inside of the [`data`] macro exported by this module,
/// as it is expanded locally rather than in the `macro_rules` definition and therefore must be in scope as well. Its primary intent is to concisely
/// add semicolons to the end of struct definitions if and only if they are required.
#[macro_export]
macro_rules! structify {
    ( $m:meta, $tname:ident, $(_)? ) => {
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

/// Generates a type-definition and associated implementations
/// of the runtime traits [`Encode`](crate::conv::Encode), [`Decode`](crate::conv::Decode), and [`FixedLength`](crate::conv::len::FixedLength)
/// for a data enum (i.e. discriminated union with at least one constructor carrying data).
///
/// For the purposes of avoiding extraneous boilerplate logic in the macro itself, the expansion
/// of this macro defines a public module `payload`, which contains individual struct definitions
/// for each variant of the enumeration being defined. The enum definition itself is then defined
/// as a union of unary constructors that are parametric over a novel payload type sharing their
/// identifier within the `payload` module scope. As an unintended consequence of this facet of the
/// macro, *it cannot be invoked more than once in the same scope*, as two modules of the same name
/// cannot both be defined within a common namespace.
///
/// # Syntax
///
/// The following syntactical conventions are adopted for the generative macro `data`:
///
/// ```ignore
/// data!( <TYPE_ID> , <REPR := (u8|u16)> , '{' <DISCR> => <CONSTR_ID> <CONSTR_PAYLOAD>  (, <DISCR> => <CONSTR_ID> <CONSTR_DEF><CONSTR_PAYLOAD>  )* ,? '}')
/// ```
///
/// where `<TYPE_ID>` is a valid and unused (in the current scope) identifier to be used as the
/// name of the enumerated type, `<REPR>` is one of the literals `u8 | u16` and determines
/// the type used to represent the numerical discriminant in serialization/deserialization,
/// and each `<DISCR> => <CONSTR_ID> <CONSTR_PAYLOAD>` sub-expression corresponds to a unique variant of the enumerated type,
/// with a mandatory explicit non-negative integral constant expression <DISRC> (ideally a numeric literal)
/// used as the in-codec representation of the constructor `<CONSTR_ID>`, which must be unique among its peers.
/// A comma must separate each association, but a trailing comma after the final variant is optional.
/// At least one constructor must be provided in order
/// for `data` to be syntactically valid, as an empty enum is not semantically sound in the context in which
/// this macro is intended to be used.
///
/// <CONSTR_PAYLOAD> is precisely the content that would appear after the name of the constructor in a standard
/// enum variant definition, i.e. `ε | TUPLE_STRUCT_DEF | RECORD_STRUCT_DEF`. For more information about the precise
/// syntax of <CONSTR_PAYLOAD>, see [`structify`], which is the utility macro responsible for producing the intermediate
/// struct definitions for the payload of each variant.
///
/// # Examples
///
/// ```
/// use crate::conv::Decode;
///
/// data!(SmallPrimeProduct, u8, { 2 => TwoPower(pub u8), 3 => ThreePower(pub u8), 5 => FivePower(pub u8) });
/// assert!(matches!(SmallPrime::decode("0501"), SmallPrimePower::FivePower(1)));
/// ```
///
/// #
///
/// ```
/// data!(NarrowUnit, u8, { 0 => Unit });
/// assert_eq(std::mem::size_of::<NarrowUnit>(), std::mem::size_of::<u8>());
/// ```
///
/// ```
/// data!(WideUnit, u16, { 0 => Unit });
/// assert_eq(std::mem::size_of::<WideUnit>(), std::mem::size_of::<u16>());
/// ```
#[macro_export]
macro_rules! data {
    { $name:ident, $backer:ident, { $( $disc:expr => $vname:ident $($vspec:tt)? ),+ } } => {
        pub mod payload {
            #![allow(non_camel_case_types)]
            use super::*;
            use $crate::FixedLength;
            $(
                $crate::structify!(derive(Encode,Decode,Estimable,Debug), $vname, $($vspec)?);
            )+
        }


        #[derive(Debug)]
        pub enum $name {
            $( $vname(payload::$vname) ),+
        }

        impl $crate::Decode for $name {
            fn parse<P: $crate::Parser>(p: &mut P) -> $crate::ParseResult<$name> {
                match p.get_tagword::<$name, $backer>(&vec![ $( $disc as $backer ),+ ])? {
                    $(
                        $disc => {
                            Ok($name::$vname(<payload::$vname>::parse(p)?))
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
                            <payload::$vname>::write(inner, buf);
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
                            <$backer as FixedLength>::LEN + <payload::$vname as Estimable>::len(inner)
                    ),+
                }
            }
        }
    }
}
