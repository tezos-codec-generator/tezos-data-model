# `rust_runtime`

The `rust_runtime` library crate contains the common utility code that generated Rustlang codec modules are built around.

Also contained in this directory are sub-crates defining derive macros for three key traits in the runtime:

- `decode_derive` for the `Decode` trait
- `encode_derive` for the `Encode` trait
- `estimable_derive` for the `Estimable` trait

As the `codec_generator` project is not yet stable, both the design, API, and implementation specifics of this crate
are subject to change at any point. On account of this, this readme may not always be up-to-date, and so reader
discretion is advised.

This README is intended to serve as a general guide for the model, and design approach, of the `rust_runtime` crate, rather
than a comprehensive summary of the actual implementation.

## High-Level Approach

The `rust_runtime` library crate is built around a model of structurally inductive transcoding using two traits:

- `Encode` :
  Trait marking a type as serializable.
  The most stable property of this trait is the definition of a method `encode` of type `(&self) -> X`, where `X` is some
  type suited for the representation of variable-length strings of binary data.
  This may either be a concrete type, or a generic-type satisfying particular trait bounds.
- `Decode` :
  Trait marking a type as deserializable.
  The most stable property of this trait is the definition of a method `decode`of type `(&X) -> Self`, where `X` is some
  type that can be interpreted as a sequence of byte-values, to be parsed in an incremental fashion.
  This may either be a concrete type, or a generic-type satisfying particular trait bounds.

These essential details are unlikely to change, and even less likely to change drastically.
Note that while the methods listed above are 'minimum requirements' in a design sense, at the level of
the trait definition, it is safe to assume that the required set of implemented methods consists of
some unspecified set of low-level methods, in terms of which `encode` and `decode` are given default implementations.

As of the time this README was last revised, all broad categories of
Ocaml-based schemata (values of type `'a Data_encoding.Encoding.t`) are
assumed to be covered by the logic of the compiler, in tandem with this
runtime library. However, that does not mean that every schemata will
be supported by the `codec_generator` pipeline, that the produced module
will be free of errors, or that an error-free codec module will be bug-free
and behave 'correctly' (i.e. equivalently to transcoding operations based directly
in Ocaml and `data-encoding`).

## Internal Approach and Abstraction

As of the current iteration of the `rust_runtime` library, the details of `Encode` and `Decode` are refined beyond the bare minimum methods listed above, and in turn rely on other definitions in the library to be used effectively. Those methods, and the constructs
they rely upon, are listed below:

- `Encode`:
  - `write_to<U: Target>(&self, buf: &mut U) -> usize` :
    Appends the full sequence of bytes of the codec-compatible serialization of `self`, to the mutably borrowed destination object,
    of a generic type bound by the trait [`Target`](#target), also defined in the runtime. The returned value is the total number of
    bytes that were written by the call.
    This is the lowest-level method, and the only one that is required for implementors to define.
  - `write_to_vec(&self, buf: &mut Vec<u8>) -> ()` :
    A variant of `write_to` specialized to `Vec<u8>`, without an informative return value. This method is given a default implementation
    in terms of `write_to` through the included `impl Target for Vec<u8>` item, but can be overwritten if a more directly efficient
    implementation is possible based on details of the `Self` type in question.
  - `to_bytes(&self) -> Vec<u8>` :
    An analogue of `write_to_vec` that returns a new `Vec<u8>` buffer rather than mutating an existing buffer passed in as an argument.
    In most cases, the default implementation (which calls `Vec::new()` followed by `Self::write_to_vec`) is adequate. In certain cases, such as when `self` is either itself, or a shallow wrapper around, a byte-oriented buffer, this definition may be overwritten with a `.clone()` or `.to_vec()` operation or similar.
  - `encode<U: Target>(&self) -> U` : produces an object of the specified or compiler-inferred type `U` subject to the trait bounds of implementing an instance of [`Target`](#target). This has a default implementation using `write_to()`.
- `Decode`:
  - `parse<P: Parser>(p: &mut P) -> Self` : uses a mutably borrowed generic object of any type implementing the [`Parser`](#parser) trait, returning a value of type `Self` by consuming from the current parser-head until enough bytes have been read to deserialize; this method will panic if the parse operation internally called returns an `Err(ParseError)` value.
  - `decode<U: ToParser>(input: &U) -> Self`: combined operation of constructing a `P: Parser` object from a [`ToParser`](#toparser) bounded generic, and calling `Self::parse` over the returned value (default implementaion). There is no compelling reason to override
  the default implementation, as it is merely intended to avoid boilerplate and does not obviously introduce any unnecessary overhead
  in any known edge-cases.

### Target

The trait `Target` is an abstraction over types that store an in-order traversible sequence of bytes, which, once written, are never
subsequently modified. In this way, it may be thought of as a specialized analogue of `std::io::Write`.

The provided implementing types of `Target` are as follows:

- `Vec<u8>`
- `std::io::Sink` via type-alias `ByteCounter`
- All implementors of [`Builder`](#builder), via a sub-trait bound

The current implementation of `Target` consists of the following methods:

- `anticipate(&mut self, extra: usize)`: Perform any amortizing operations under the assumption that at least `extra` more bytes will be written over an unknown number of individual method calls. The main use of this method is in the blanket implmentation over the schema-specific `Dynamic<S, T>` type, where the serialized byte-length of the contained value of type `T: Encode` is known in advance of the calls made to actually serialize it.
- `create() -> Self`: Factory method to replace `Vec::new()` or `Builder::empty()` as appropriate
- `push_one(&mut self, b: u8) -> usize`: Appends a single byte to the Target object. Will and must always return `1`.
- `push_many<const N: usize>(&mut self, arr: [u8; N]) -> usize`: Appends a constant-length byte array, in order, to the Target object. Will and must always return `N`
- `push_all(&mut self, b: &[u8]) -> usize`: Appends a byte-slice of unknown length to the Target object, in order. Will and must always return the length of the slice.
- `resolve(&mut self)`: When applicable, indicate in some fashion that the current final index of the byte-sequence is a partition point between two logically distinct serialized values. Most of the time, this method will be a no-op.

#### Target-related Macros

In addition to the

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

- A fresh `p : impl Parser` object should have `p.offset() == 0` and `p.len()` equal to the length of the parse-buffer
- `self.len() - self.offset()` is the largest possible `n` for which `self.consume(n)` returns an `Ok(_)` value, which should also be the largest possible `n` for which `self.set_fit(n)` succeeds. Both should fail for any greater values of `n`, either through `Err(_)` returns or panics.
- The value of `self.len() - self.offset()` before and after a call to `self.consume(n)` should represent a decrease by `n` if the consume call is an `Ok(_)` value, or remain unchanged if it is an `Err(_)` value. Only one of `self.len()` and `self.offset()` should change in this fashion.
- `self.set_fit(m)` should fail whenever `self.len() < m + self.offset()`, and succeed otherwise
- Immediately after a successful call of `self.set_fit(n)`, `self.len() == n + self.offset()` should hold.
- `self.test_target()` should return `true` if and only if `self.offset() == self.len()` holds with at least one context window present
- `self.enforce_target()` should remove the most recently set target if `self.test_target()` would return true, and panic otherwise

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
