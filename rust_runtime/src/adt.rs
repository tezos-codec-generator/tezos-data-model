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
/// # use rust_runtime::{Decode, cstyle, hex};
///
/// cstyle!(SmallPrime, u8, { Two = 2, Three = 3, Five = 5, Seven = 7 });
/// assert_eq!(SmallPrime::Five as u8, 5u8);
/// assert_eq!(SmallPrime::decode(vec![0x05u8]) as u8, SmallPrime::Five as u8);
/// ```
///
/// #
///
/// ```
/// # use ::rust_runtime::cstyle;
/// cstyle!(NarrowUnit, u8, { Unit = 0 });
/// cstyle!(WideUnit, u32, { Unit = 0 });
/// assert_eq!(std::mem::size_of::<NarrowUnit>(), 1);
/// assert_eq!(std::mem::size_of::<WideUnit>(), 4);
/// ```
///
#[macro_export]
macro_rules! cstyle {
    ( $name:ident, $backer:ident, { $( $vname:ident = $vdisc:expr ),+ } ) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[repr($backer)]
        pub enum $name {
            $( $vname = $vdisc ),+
        }

        impl $crate::Decode for $name {
            fn parse<P: $crate::Parser>(p: &mut P) -> $crate::ParseResult<$name> {
                match p.take_tagword::<$name, $backer>(&vec![ $($vdisc as $backer),+ ])? {
                    $(
                        $vdisc => Ok($name::$vname),
                    )+
                    _ => unreachable!(),
                }
            }
        }

        impl $crate::Encode for $name {
            fn write_to<U: $crate::Target>(&self, buf: &mut U) -> usize {
                let tag : $backer = match self {
                    $(
                        $name::$vname => $vdisc
                    ),+
                };

                tag.write_to(buf)
            }
        }

        impl $crate::FixedLength for $name {
            const LEN : usize = <$backer>::LEN;
        }
    }
}

/// Generate the boilerplate for an enum type with explicit discriminant values
///
/// This macro is the standard means offered by this crate for defining tagged unions
/// over variants at least one of which has associated data (or 'data-enum').
///
/// As Rust does not (yet) support user-specified discriminant values for data enums,
/// the actual tag-values that the compiler decides to use for the variants cannot
/// be controlled, and has no bearing on what the interoperable discriminant value
/// for each variant is, according to a `data-encoding` schema.
///
/// Instead, the association of user-specified numbers with corresponding variants,
/// is handled within the boilerplate logic for transcoding values of the novel type,
/// as described below.
///
/// # General Layout
///
/// This macro produces both a top-level definition for the enumerated type,
/// and a series of trait implementations corresponding to the natural
/// definitions on that type of:
///   * [`Encode`](../conv/trait.Encode.html)
///   * [`Decode`](../conv/trait.Decode.html)
///   * [`Estimable`](../conv/len/trait.Estimable.html)
///
/// The implementations of `Encode` and `Decode` generated in this fashion, define the
/// mapping between each constructor and the tag-value it should be associated with.
/// As it is implemented, no mechanism exists for determining, without attempting to
/// encode or decode a dummy value, the tag-value for a given constructor, or the
/// constructor for a given tag-value.
///
/// # Syntax
///
/// The following syntactical conventions are adopted for the generative macro `data`:
///
/// ```ignore
/// data!(TYPE_ID, REPR, PAYLOAD_SUBMODULE_ID, { ( <DISCR> => <CONSTR_ID> <CONSTR_PAYLOAD> ,)+ '}')
/// ```
///
/// The elements of this specification are described below:
///   * `TYPE_ID` is a valid and locally unique type-id. This is the name of the enum-type, i.e. `pub enum <TYPE_ID> { ... }`
///   * `REPR` must be one of the literals `u8` or `u16`, and determines which of those primitive types is used for the schema-compatible discriminant
///     of the data-enum. This choice is always dictated by the schema definition and cannot be chosen arbitrarily.
///   * `PAYLOAD_SUBMODULE_ID` is a valid and locally unique submodule-id. It is used as a literal identifier for
///     the submodule that holds the extracted struct-definitions for the data associated with each variant.
///     These structs will inherit the name of the constructor holding them, and will be given derived implementations
///     of an assortment of traits listed further down.
///   * A non-empty sequence consisting of elements composed of the sequence:
///       * `DISCR`: Unique numeric literal (constant expressions allowed but
///       discouraged) for the schema-compatible discriminant of the following
///       variant. This must be in range of the chosen `<REPR>` type
///       * `=>` as a literal token
///       * `CONSTR_ID`: Unique identifier for both the variant, and the struct defined in the payload submodule,
///         associated with the preceding tag-value. PascalCase is not enforced, but Rust reserved keywords
///         are disallowed and must be sanitized or turned into raw identifiers.
///       * `CONSTR_PAYLOAD`: The constructor payload that would follow its name in native enum syntax.
///         i.e. `ε | TUPLE_STRUCT_DEF | RECORD_STRUCT_DEF`.
///
/// # Syntax Notes
///
/// A quirk of the way this macro is written is that if the final declared variant happens to have no
/// payload (i.e. `CONSTR_PAYLOAD = ε`), the trailing comma is mandatory for syntactic validity.
///
/// Furthermore, whenever a type identifier within the payload of a constructor happens to coincide
/// with the name of the constructor itself, it must be qualified in such a way as to disambiguate
/// the contained value-type from the constructor name, as the latter becomes a type identifier when
/// converted to a struct definition in the payload module, and therefore shadows any extant imports
/// under the same name. For example, while
///
/// ```ignore
/// pub enum Foo {
///     String(String),
/// }
/// ```
///
/// is unambiguous,
///
/// ```ignore
/// data!(Foo, u8, payload, { 0 => String (String) }); // does not compile
/// ```
///
/// expands to
///
/// ```ignore
/// pub mod payload {
///     /* ... */
///     pub struct String(String); // does not compile
///     /* ... */
/// }
/// /* ... */
/// ```
///
/// which inadvertently causes `std::string::String` to be shadowed under its unqualified name, and
/// due to direct recursion, this will not even compile. To avoid this, qualify any ambiguous type-ids
/// that would otherwise be shadowed:
///
/// ```ignore
/// data!(Foo, u8, payload, { 0 => String (std::string::String) });
/// ```
///
/// Note that this will occur even *across* constructors as they are all defined in the same submodule
/// scope, so extra care is required even when the shadowing occurs accross variant definitions rather
/// than within an isolated variant definition.
///
/// It is never correct to define a data-enum with even indirect recursion on one of its own payload types,
/// as payload types are an artifact of this macro and would not normally exist as an in-scope type identifier;
/// therefore, the automatic resolution of ambiguous type identifiers will never be correct, and qualification
/// is therefore always required.
///
/// # Semantics
///
/// By necessity, the enum-type definitions this macro produces do not actually
/// hold the expected payload, but instead a single argument of a payload type
/// defined in the appropriately named payload module (see
/// `PAYLOAD_SUBMODULE_ID` under Syntax).  Each such module module contains the
/// individual struct definitions for each variant of the enum being defined,
/// with the following derived trait implementations:
///   * Crate defined traits: `Encode`,`Decode`,`Estimable`
///   * Standard library traits: `Debug`, `Clone`, `PartialEq`, `PartialOrd`
///
/// # Examples
///
/// ```
/// # #[macro_use] extern crate rust_runtime;
/// # use ::rust_runtime::conv::Decode;
/// data!(SmallPrimePower, u8, payload, { 2 => TwoPower(pub u8), 3 => ThreePower(pub u8), 5 => FivePower(pub u8) });
/// assert_eq!(SmallPrimePower::decode(hex!("0501")), SmallPrimePower::FivePower(payload::FivePower(1)));
/// ```
///
/// ```
/// # #[macro_use] extern crate rust_runtime;
/// # use rust_runtime::conv::EncodeLength;
/// data!(WideUnit, u16, payload, { 0 => Unit, });
/// assert_eq!(EncodeLength::enc_len(&WideUnit::Unit(payload::Unit)), EncodeLength::enc_len(&0u16));
/// assert_eq!(EncodeLength::enc_len(&payload::Unit), EncodeLength::enc_len(&()));
/// ```
#[macro_export]
macro_rules! data {
    (@structify $m:meta, $tname:ident, $(,)? ) => {
        #[$m]
        pub struct $tname;
    };
    (@structify $m:meta, $tname:ident, () ) => {
        #[$m]
        pub struct $tname;
    };
    (@structify $m:meta, $tname:ident, ( $( $v:vis $i:ty ),+ )) => {
        #[$m]
        pub struct $tname( $( $v $i),+ );
    };
    (@structify $m:meta, $tname:ident, { $( $v:vis $x:ident : $y:ty ),+ }) => {
        #[$m]
        pub struct $tname { $( $v $x : $y ),+ }
    };
    { $name:ident, $backer:ident, $payload:ident, { $( $disc:expr => $vname:ident $vspec:tt $(,)? )+ } } => {

        pub mod $payload {
            #![allow(non_camel_case_types)]
            use super::*;
            use $crate::{Encode, Decode, Estimable};
            $(
                $crate::data!(@structify derive(Encode,Decode,Estimable,Debug,Clone,PartialEq,PartialOrd,Hash), $vname, $vspec);
            )+
        }


        #[derive(Clone, PartialEq, PartialOrd)]
        pub enum $name {
            $( $vname($payload::$vname) ),+
        }

        impl std::hash::Hash for $name {
            fn hash<H>(&self, state: &mut H)
            where
                H: std::hash::Hasher
            {
                match self {
                    $(
                        $name::$vname(inner) => {
                            <$backer as std::hash::Hash>::hash(&$disc, state);
                            <$payload::$vname as std::hash::Hash>::hash(&inner, state)
                        }
                    )+

                }
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    $(
                        $name::$vname(inner) => write!(f, "#{:?}", inner),
                    )+
                }
            }
        }

        impl $crate::Decode for $name {
            fn parse<P: $crate::Parser>(p: &mut P) -> $crate::ParseResult<$name> {
                match p.take_tagword::<$name, $backer>(&vec![ $( $disc as $backer ),+ ])? {
                    $(
                        $disc => {
                            Ok($name::$vname(<$payload::$vname>::parse(p)?))
                        }
                    )+
                    _ => unreachable!(),
                }
            }
        }

        impl $crate::Encode for $name {
            fn write_to<U: $crate::Target>(&self, buf: &mut U) -> usize {
                match self {
                    $(
                        $name::$vname(inner) => {
                            $crate::write_all_to!($disc as $backer, inner => buf)
                        }
                    )+
                }
            }
        }

        impl $crate::Estimable for $name {
            const KNOWN : Option<usize> = None;

            fn unknown(&self) -> usize {
                match self {
                    $(
                        $name::$vname(inner) =>
                            <$backer as $crate::FixedLength>::LEN + <$payload::$vname as $crate::Estimable>::estimate(inner)
                    ),+
                }
            }
        }
    }
}
