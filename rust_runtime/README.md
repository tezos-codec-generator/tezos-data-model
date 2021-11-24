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

The trait `Builder` is an abstraction over types representing fragments of an intermediate type that can ultimately be finalized and written as a byte-vector, hex-string, or binary string. It includes trait bounds that allow homogenously typed Builders to be
concatenated using a monoidal append operation by way of the `+` operator or its `std::ops::Add::add` form.

### Parser

The trait `Parser` is an abstraction over types representing a stateful parse-object, which has default implementations for a variety of monomorphic `get_*` methods in terms of primitive required methods, including `.len()` and `.offset()` for querying internal state, and state-mutational method `.consume(nbytes)`, and the context-window operations `.set_fit(n)`, `.test_target()`, and `.enforce_target()`. It also has a trait bound of `Iterator<Item = u8>` that exposes the `.next() -> Option<&u8>` method to the monomorphic parser default implementations, which is used for `get_u8`, `get_i8`, and `get_bool`.

#### Context Windows

In order to facilitate bounds-setting and bounds-checking for dynamically sized elements with length prefixes,
we use a model of *context windows*, which are conceptually (though not necessarily implementationally) a stack
of target offsets, which may in fact be decremented counters in the case of slice-based parsers, or fixed values
of the mutating parse-head for buffer-based implementations such as [`ByteParser`](#byteparser).

The following properties should be respected by each implementation of the `Parser` trait:

* A fresh `p : impl Parser` object should have `p.offset() == 0` and `p.len()` equal to the length of the parse-buffer
* `self.len() - self.offset()` is the largest possible `n` for which `self.consume(n)` returns an `Ok(_)` value, which should also be the largest possible `n` for which `self.set_fit(n)` succeeds. Both should fail for any greater values of `n`, either through `Err(_)` returns or panics.
* The value of `self.len() - self.offset()` before and after a call to `self.consume(n)` should represent a decrease by `n` if the consume call is an `Ok(_)` value, or remain unchanged if it is an `Err(_)` value. Only one of `self.len()` and `self.offset()` should change in this fashion.
* `self.set_fit(m)` should fail whenever `self.len() < m + self.offset()`, and succeed otherwise
* Immediately after a successful call of `self.set_fit(n)`, `self.len() == n + self.offset()` should hold.
* `self.test_target()` should return `true` if and only if `self.offset() == self.len()` holds with at least one context window present
* `self.enforce_target()` should remove the most recently set target if `self.test_target()` would return true, and panic otherwise

#### ByteParser

`ByteParser` is the included implementor of `Parser`, which operates on an approach of holding an immutable buffer of bytes and a mutable offset-tracker. The context-window methods are propogated to the offset-tracker itself, which is responsible for determining
the current state of the parser, and is the only mutable element of the `ByteParser`.

#### ToParser

The `ToParser` trait is used to indicate how values of various types are to be pre-processed into a fresh `ByteParser` object.
This is done via the `.to_parser()` method, which is the only exposed method and must be defined by each implementer. In a
context where `ByteParser` has been replaced by an alternate `Parser` implementer, the return type for `.to_parser()` should be revised.

There is a slight ambiguity as to whether the `.to_parser()` definition for `String` and `&str` should assume the string is formatted as raw binary or expanded 2-byte hex words, in which the former is more natural but has corner cases in which the byte sequence we wish to
represent could not be coerced into a `String` for whatever reason (either `0x00` or malformed unicode sequences). As of the current
implementation, `String` and `&str` are treated as raw binary byte-strings, though this may change.

### HexString

`HexString` is a newtype around `Vec<u8>` that is used as an intermediate for serialization, and a pre-processed value for explicit
hexadecimal interpretation of `&str` values we wish to parse via `ToParser::to_parser()`. It exposes a `hex!()` macro that performs
conversion from a `String`, `&str`, or various `u8`-buffer (array, slice, vector) types into a `HexString`, which may panic if the
conversion cannot be performed.
