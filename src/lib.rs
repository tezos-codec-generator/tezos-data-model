//! Model for representing and transcoding data types in the Tezos protocol
//!
//! # Overview
//!
//! This library and its associated crate serve as a backbone for the machine-generation of
//! Rust modules that represent individual data types in the Tezos protocol. Such modules,
//! referred to as 'codecs' in the parlance of the original project `codec_generator` that this
//! crate is a derivative of, would normally require a great deal of boilerplate, both for generic
//! low-level serialization and deserialization tasks, and complex logic tailored to the primary
//! and auxiliary types of the original 'schema'.
//!
//! Rather than forcing the generator logic to write bespoke structures and logic for relatively
//! ubiquitous patterns, `tedium` offers a centralized implementation of common types and traits
//! that allow for derivable transcoding implementations based on a structurally inductive paradigm.
//! 'Primitive' and 'composite' types, which represent low-level data objects and functors, form
//! the core of each machine-generated type, with ad-hoc types such as records, tuples, and algebraic
//! types supported via macros.
//!
//! A number of aspects of this library offer end-users the option to hand-write implementors of the
//! core library traits, to provide specialized parsers and serialization targets.
//!
//! The high-level traits `Encode` and `Decode` are the keystones of the `tedium` library. They
//! respectively define methods for serialization and deserialization of Rust-based analogues
//! for Tezos-relevant OCaml types , to and from the proprietary binary
//! encoding scheme described and defined by the `data-encoding` (OCaml) library.
//!
//! # Background
//!
//! The `data-encoding` library, developed and maintained by Nomadic Labs, is the de facto
//! serialization/deserialization format of 'Octez' (the canonical implementation of the Tezos protocol, written in OCaml).
//! Virtually all constants, parameters, and values that are defined and used within the Tezos ecosystem,
//! across various contexts and formats, originate as instances of OCaml types, whose binary representation strategies
//! are declared in the Domain-Specific Language of `data-encoding` primitives and combinators.
//!
//! For the purposes of writing any sort of client library that interacts with such values, it is
//! necessary to establish a consistent and interoperable view of, at the very least, the subset of data-types that
//! are of relevance to the library's intended functionality. Furthermore, as new protocol versions
//! are proposed and introduced on-chain, any code that deals with protocol-specific type-definitions
//! can become obsolete or unsafe with each new release. As a consequence, there is a continual burden
//! imposed on developers of maintaining their type definitions and associated logic, so that it remains
//! in sync with the raw data coming in from various sources.
//!
//! In order to facilitate more seamless and reliable interoperability
//! between client libraries and the Tezos economic protocol, the [`codec_generator`] project
//! is designed to provide automatic compilation from the associated encoding-schemas of Tezos-relevant OCaml types
//! into *codec* modules in various languages and formats.
//!
//! This library serves as an analogous model for the structural encoding specifications of
//! the `data-encoding` library, that can facilitate more lightweight *codec* generation by
//! eliminating as many lines of boilerplate as possible, from each generated file. Simultaneously,
//! it also defines the type-language in which such codec types are expressed, such that downstream
//! consumers of such code can interpret and operate on machine-generated codecs in more consistent
//! and predictable ways.
//!
//! [`codec_generator`]: Originally a separate project known as `tezos-codec-compiler`.

extern crate decode_derive;
extern crate encode_derive;
extern crate estimable_derive;

pub mod adt;
pub mod autobox;
pub mod builder;
pub mod conv;
pub mod dynamic;
pub mod error;
pub mod fixed;
pub mod float;
pub mod hexstring;
pub mod int;
mod internal;
pub mod parse;
pub mod prelude;
pub mod prim;
pub mod schema;
pub mod seq;
pub mod zarith;

#[cfg(feature = "expose_internal")]
pub use crate::internal;

pub use crate::autobox::AutoBox;
pub use crate::builder::{memo::MemoBuilder, strict::StrictBuilder, Builder};
pub use crate::conv::{
    len::{Estimable, FixedLength, ScalarLength},
    target::Target,
    Decode, Encode,
};
pub use crate::dynamic::{Dynamic, VPadded};
pub use crate::fixed::{FixedBytes, FixedString};
pub use crate::float::RangedFloat;
pub use crate::hexstring::HexString;
pub use crate::int::{i31, u30, RangedInt};
pub use crate::parse::{
    byteparser::ByteParser, error::ParseError, memoparser::MemoParser, sliceparser::SliceParser,
    ParseResult, Parser, TryIntoParser,
};
pub use crate::schema::{Bytes, Nullable, Padded};
pub use crate::seq::{fix::FixSeq, lim::LimSeq, Sequence};
pub use crate::zarith::{n::N, z::Z};
pub use prelude::{ByteString, CharString};

pub use ::decode_derive::Decode;
pub use ::encode_derive::Encode;
pub use ::estimable_derive::{Estimable, FixedLength};
pub use ::lazy_static::lazy_static;
