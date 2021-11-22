# `rust_runtime`


This directory is a collection of `Rustlang` packages and crates that constitute the core API used by the generated `*.rs` codec-modules that `codec_generator` produces.

As the overall project evolves, the strucural layout of the toplevel and subordinate crates may change drastically, as too may the implementation details within the runtime API, along with the API itself.

This README is intended to act as a loose guide for the model and design approach of the `rust_runtime` crate and its associated subordinate crates, so that the impact of under-documentation in the Rust modules themselves is somewhat mitigated.

## High-Level Approach

The `rust_runtime` library crate is built around a model of structurally inductive transcoding using two traits:

* `Encode` : at minimum, defines a method `encode` of type `(&self) -> X`, where X is a type suitable for byte-level concatenation and traversal. This may be just `Vec<u8>` or similar, a wrapper around such a builtin type, or even a generic type parameter satisfying certain trait bounds that ensure it is suitable for use as a byte-store.
* `Decode` : at minimum, defines a method `decode` of type `(&X) -> Self`, where X is the type of incoming binary data to be parsed with byte-level precision. This may be just `Vec<u8>` or similar, a wrapper around such a builtin type,
  or even a generic type parameter satisfying certain trait
  bounds that ensure it is suitable for incremental parsing.

These minimum details are unlikely to change, though the actual implementation of the traits themselves, with regard to which additional methods are required, and whether certain methods have default implementations with respect to lower-level methods, are subject to refactoring as the project grows.

Manual and blanket implementations of these traits for the majority of relevant `Rustlang` primitives, as well as for more complex `data-encoding`-specific schema types, are added according to the project milestones in the [main README](../README.md). Based on
those atomic types, and combinatorial logic for incremental parsing and serialization of Product- and Sum-types, it is theoretically
possible, once support for all of the possible `data-encoding` schema type AST nodes is modeled in the `runtime` logic, to define
and use `Encode` and `Decode` methods over any OCaml type whose intended binary layout is expressible as a `Data_encoding.t` value.

## Internal Approach and Abstraction

As of the current iteration of the `rust_runtime` library, the details of `Encode` and `Decode` are refined beyond the bare minimum methods listed above, and in turn rely on other definitions in the library to be used effectively. Those methods, and the constructs
they rely upon, are listed below:

* `Encode`:
  * `write(&self, buf: &mut Vec<u8>) -> ()` : writes the byte-sequence corresponding to the codec-compatible serialization of `self` to a mutably borrowed byte-buffer. This is the lowest-level method, and the only one that is required for implementors to define.
  * `to_bytes(&self) -> Vec<u8>` : returns a byte-sequence corresponding to the serialization of `self`. This method has a default implementation of allocating a new `Vec<u8>` which is passed into a call to `self.write`. In certain cases, such as when `self` is internally a byte-array or even a byte-vector, this definition may be overwritten with a `.clone()` or `.to_vec()` operation.
  * `encode<U: Builder>(&self) -> U` : produces an object of the specified or compiler-inferred type `U` subject to the trait bounds of implementing an instance of [`Builder`](#builder). This has a default implementation using `to_bytes()`.
* `Decode`:
  * `parse<P: Parser>(p: &mut P) -> Self` : uses a mutably borrowed generic object of any type implementing the [`Parser`](#parser) trait, returning a value of type `Self` by consuming from the current parser-head until enough bytes have been read to deserialize; this method will panic if the parse operation internally called returns an `Err(ParseError)` value.
  * `decode<U: ToParser>(input: &U) -> Self`: combined operation of constructing a `P: Parser` object from a [`ToParser`](#toparser) bounded generic, and calling `Self::parse` over the returned value (default implementaion). There is no compelling reason to override
  the default implementation, as it is merely intended to avoid boilerplate and does not obviously introduce any unnecessary overhead
  in any known edge-cases.

### Builder

The trait `Builder` is a combination of a number of helpful trait bounds, and a selection of helper methods, designed to provide
a layer of abstraction between the kinds of operations and features we want to define for all serialization objects, and the specific ways in which they are to be implemented.

#### OwnedBuilder

### Parser

#### ByteParser

### HexString