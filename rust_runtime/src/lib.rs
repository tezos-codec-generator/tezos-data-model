//! Rust(lang) Runtime for the OCaml-based `data-encoding` codec-generator pipeline
//!
//! # Overview
//!
//! This crate is both an implementation of, and implicitly a general API specification for,
//! the common Rust and domain-specific constructions that are imported and used by the Rust
//! codec modules that are compiled by the codec generator pipeline that exists as a semi-independent
//! sub-project of the OCaml `data-encoding` library. Though the exact details of the API are not
//! yet rigid, the general design is centered around the traits `Encode` and `Decode`, which
//! respectively define the methods required for serialization and deserialization between the
//! binary data representing an OCaml type via `data-encoding`, and the imputed form of its Rust-based
//! equivalent type. Each codec module will typically consist of a type-definition or type-alias for
//! the codec type represented in the original schema being compiled, and either machine-generated
//! or derive-macro facilitated implementations of `Encode` and `Decode` on that type, provided
//! it is not an alias for a type with such implementations already defined in this library.
//!
//! # Background
//!
//! The `data-encoding` library, developed and maintained by Nomadic Labs, is the de facto
//! serialization/deserialization format of the `octez` implementation of the Tezos protocol.
//! Virtually all constants, parameters, and values that are defined and used within the Tezos
//! economic protocol, whether in P2P communication, RPC calls, or in on-disc storage, originate
//! as instances of OCaml types, whose binary formats are declared in the DSL of `data-encoding`
//! primitives and combinators.
//!
//! For the purposes of writing any sort of client library that interacts with such values, it is
//! necessary to establish a consistent and interoperable view of the subset of value-types that
//! are relevant to the library's scope. Furthermore, as new protocol versions
//! are voted in, newly introduced or otherwise changed definitions of existing protocol types
//! must also be reflected in the library as well. The status quo requires that this be done by hand, consulting either documentation or `octez` source-code
//! to infer the intended structure and use of each new or modified type-definition, which in turn
//! necessitates a certain level of literacy in `Ocaml` that may not always be sufficient in light of
//! the intricacies of the `data-encoding` DSL and the complex and widely inter-connected nature
//! of the `Octez` source-tree.
//!
//! In order to facilitate more seamless and reliable continuous integration and interoperability
//! between client libraries and the Tezos economic protocol, the [`codec_generator`] sub-project
//! of the `data-encoding` library aims to provide automatic compilation from the original binary
//! encoding specification of a type, into *codec* modules in arbitrary target languages, to the
//! extent that there are client libraries written in those languages that could make use of this
//! aid.
//!
//! Rather than hand-roll the entire set of low-level type definitions and functions required for
//! parsing a simple codec when compiling each schema, this crate serves as a static runtime for
//! machine-generated codec modules to code against, which means that common definitions can be
//! imported instead of redefined, and the process of review and debugging can be done against
//! a static crate rather than a theoretical set of definitions hard-coded as boilerplate Rust AST
//! values in OCaml sourcefiles.
//!
//! [`codec_generator`]: Originally a separate project known as `tezos-codec-compiler`

extern crate decode_derive;
extern crate encode_derive;
extern crate estimable_derive;

pub mod adt;
pub mod autobox;
pub mod builder;
pub mod conv;
pub mod default;
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
pub mod zarith;

pub use crate::autobox::AutoBox;
pub use crate::builder::{memo::MemoBuilder, strict::StrictBuilder, Builder};
pub use crate::conv::{
    len::{Estimable, FixedLength, ScalarLength},
    target::Target,
    Decode, Encode,
};
pub use crate::dynamic::{Dynamic, VPadded};
pub use crate::fixed::{bytes::FixedBytes, string::FixedString};
pub use crate::float::RangedFloat;
pub use crate::hexstring::HexString;
pub use crate::int::{i31, u30, RangedInt};
pub use crate::parse::{
    byteparser::ByteParser, error::ParseError, memoparser::MemoParser, sliceparser::SliceParser,
    ParseResult, Parser, TryIntoParser,
};
pub use crate::schema::{
    seq::{fix::FixSeq, lim::LimSeq, Sequence},
    Bytes, Nullable, Padded,
};
pub use crate::zarith::{n::N, z::Z};
pub use prelude::{ByteString, CharString};

pub use ::decode_derive::Decode;
pub use ::encode_derive::Encode;
pub use ::estimable_derive::Estimable;
pub use ::lazy_static::lazy_static;
