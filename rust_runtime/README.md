# `runtime`/`rust_runtime`

The `runtime` package consists of a library, `rust_runtime`, with common utility
code for codec modules generated in the Rust language, through the
`codec_generator` compilation pipeline.

As the project is still under experimental development, many aspects of `runtime`
may be subject to change as it evolves: the name of the package itself or the library
it contains, where it is hosted, the overall API design, its dependency list, and
its implementation details are among these variable details.

Consequently, the outline and description provided here may refer to renamed,
relocated, redesigned, and even removed items, though efforts to keep it up-to-date
are ongoing. Nevertheless, reader discretion is advised, and documentation comments
local to the package may be more accurate on a case-by-case basis.

This document is intended to serve as a general guide to the package, in terms of
the design model it is based on, and pertinent API details, especially those that
are less likely to be changed drastically. Specific implementation details may
be found in the in-library documentation as applicable.

## Overview

The `rust_runtime` library is intended to provide a flexible and potentially
interchangeable framework, in terms of which lightweight and portable codec
modules can be produced. This requires a certain amount of API-specific
hard-coding in the `codec_generator` tool itself, but most of the implementation
details are kept opaque so that they may be changed according to the evolving
and potentially conflicting requirements of the potential adopters of this
project's approach.

The primary role of the library consists of simplifying the boilerplate
requirements of specifying the serialization/deserialization strategies
of user-defined types. To that end, two core *traits* are defined by
the library, one for serialization and one for deserialization, along
with a set of custom primitive and complex types specific to the
`data-encoding` schema, which can be used as building-blocks of
arbitrarily complex (at least in theory) codec type definitions.

### High-Level Approach

The `rust_runtime` library is built around a model of structurally inductive transcoding using two traits:

- `Encode` :
  Trait marking a type as serializable.
  The most stable property of this trait is the definition of a method `encode` of type `fn(&self) -> X`, where `X` is some
  type suited for the representation of variable-length byte-sequences.
  `X` may either be a concrete type, or a generic-type satisfying appropriate trait bounds.
- `Decode` :
  Trait marking a type as deserializable.
  The most stable property of this trait is the definition of a method `decode` of type `fn(X) -> Self`, where `X` is some
  type that has a natural interpretation as serial binary data, to be parsed according to the structural definition of the
  implementing type in question.
  `X` may either be a concrete type, or a generic-type satisfying appropriate trait bounds.

These essential details are unlikely to change, and even if they do, they are fundamental enough that
such changes should be minor.

Note that while the methods listed above are 'essential requirements' in a design sense,
they are currently given default implementations in terms of lower-level methods of the
respective traits, and are therefore not 'required methods' of the trait as far as
the Rust compiler is concerned.

As of the time this README was last revised, all broad categories of Ocaml-based
schemata (values of type `'a Data_encoding.Encoding.t`) are assumed to be
covered by the logic of the compiler, in tandem with this runtime library.
However, that does not mean that every schema will be supported by the
`codec_generator` pipeline, that the produced module will be free of errors, or
that an error-free codec module will be bug-free and behave 'correctly' (i.e.
equivalently to transcoding operations based directly in Ocaml and
`data-encoding`).

### Internal Approach and Abstraction

As of the current iteration of the `rust_runtime` library, the details of
`Encode` and `Decode` are refined beyond the bare minimum methods listed above,
and in turn rely on other definitions in the library to be used effectively.
Those methods, and the constructs they rely upon, are listed below:

- `Encode`:
  - `write_to<U: Target>(&self, buf: &mut U) -> usize` :
    Appends the full sequence of bytes of the codec-compatible serialization of
    `self`, to the mutably borrowed destination object, of a generic type bound
    by the trait [`Target`](#target), also defined in the runtime. The returned
    value is the total number of bytes that were written by the call. This is
    the lowest-level, and the only required (non-default) method.
  - `write_to_vec(&self, buf: &mut Vec<u8>)` :
    A variant of `write_to` specialized to `Vec<u8>`, without an informative
    return value. This method is given a default implementation in terms of
    `write_to` based on the definition of `impl Target for Vec<u8>`. However,
    for certain types predisposed to array-like operations, this method may be
    overridden with a more direct implementation.
  - `encode<U: Target>(&self) -> U`:
    Combines the semantics of `write_to` with the creation of a novel
    `U: Target` object, instantiating and returning a `U`-value containing
    the full serialization of `self`. This method is given a default implementation
    that should only realistically be overwritten for zero-width codecs.
  - `to_bytes(&self) -> Vec<u8>` :
    Derivative method of `write_to_vec` that creates a new `Vec<u8>` instead of taking
    one as an argument. The return value is this novel buffer after it has been populated
    using `write_to_vec`.
    As with the method it is based on, already array-like types may be able to implement
    this method more efficiently than the default definition, such as using `Vec::clone` or
    `to_vec()` methods on certain `u8`-oriented array-like types.
- `Decode`:
  - `parse<P: Parser>(p: &mut P) -> ParseResult<Self>` :
    Consumes and interprets bytes from from a mutably borrowed value
    of a generic type `P` implementing the [`Parser`](#parser) trait.
    It is expected and intended that this method short-circuit on `Err(_)` values
    returned by any internal calls to `Parser` methods or other `<T as Decode>::parse`
    calls, which is facilitated by the `?` operator. If no error is encountered, the
    return value will be `Ok(val)` where `val: Self` is the interpreted value of the
    consumed bytes.
  - `try_decode<U, P>(input: U) -> DecodeResult<Self>`:
    Converts an `input` value of type `U: TryIntoParser<P>` where `P: Parser`,
    parses it according to `Self::parse`. If either the conversion from `input`
    into a parser object, or the parse operation itself results in failure,
    the corresponding error is returned, wrapped in the broader error-type
    `DecodeError`. Otherwise, the return value will be that of the `parse` call.
    If the feature-flag `"check_complete_parse"` is explicitly enabled,
    this method will also perform a post-check to ensure that no extraneous
    bytes were left in the parser's buffer following the `parse` operation,
    returning an indicative error if this condition is violated. While normally
    this kind of validation is unnecessary and imposes overhead on every
    `try_decode` operation, it is potentially desirable to catch implementation
    bugs that might otherwise go unnoticed when the incompletely consumed parser
  - `decode_memo<U>(input: U) -> Self`:
    Derived method of `try_decode` specialized to the [`MemoParser`](#memoparser)
    type, which attempts to unwrap the result of `try_decode<U, MemoParser>(input)`
    in the default implementation. This method is intended primarily for debugging
    purposes while the project is still experimental, and may be deprecated later on.
  - `decode<U>(input: U) -> Self`:
    Derived method of `try_decode` specialized over [`ByteParser`](#byteparser),
    which, like `decode_memo`, panics instead of propogating any errors returned
    by `try_decode`.

## Auxilliary Traits

In addition to `Encode` and `Decode`, this library defines a small number of auxilliary
traits related specifically to the tasks of serialization/deserialization, but which
are neither specific to the schema language of `data-encoding`, nor inextricably
tied to the design of `Encode` and `Decode`. Nevertheless, these traits are variously
relied upon in the current definitions of `Encode` and `Decode`, even if only
by name and not necessarily by implementation specifics.

### Parser

The `Parser` trait is used to define a common set of primitive operations on
a variety of parser models, based on a small selection of low-level methods.
The following are the essential requirements for a `Parser` implementation:

- The associated type `Buffer`, into which an offset is maintained and whose binary data is consumed incrementally
- A constructor `from_buffer(buffer: Self::Buffer) -> Self`, which should never fail
- The state-query methods:
  - `.view_len()`
  - `.offset()`
- The context-window manipulation methods:
  - `.set_fit(n: usize) -> ParseResult<()>`
  - `.test_target() -> ParseResult<bool>`
  - `.enforce_target() -> ParseResult<()>`
- The primitive consume operations:
  - `consume_byte(&mut self) -> ParseResult<u8>`
  - `consume(&mut self, nbytes: usize) -> ParseResult<&[u8]>`
- `cleanup(mut self)`, which handles the validated cleanup of a potentially underconsumed parser

In terms of these methods, `Parser` provides default implementations for a
variety of operations named `take_*`, which consume a certain number of bytes
and return a value of a certain type, in both cases specific to the method in
question.

Though not a trait bound, the provided implementations of `Parser` also implement
`Iterator<Item = u8>`, based on the `Parser::consume_byte` method.

#### Context-Windows

In order to facilitate bounds-setting and bounds-checking for dynamically sized elements with length prefixes,
we use a model of *context windows*, which are conceptually a stack
of monotonically (but not always strictly) narrowing target offsets.

Until it is properly closed, a *context window* presents an inescapable narrowed view of the buffer
in question, and any consume-based operation that would require more bytes than are in the current-narrowest
context-window is contractually mandated to return an error.

The term 'context-frame', or simply 'frame', is also used to refer to the same model, while
'target-offset' specifically refers to the end of a given window.

#### Parser Invariants

The following properties should be respected by each type `P` that implements `Parser`:

1. For a buffer `buf` containing `N` bytes, with the assignment `let p = P::from_buffer(buf)`:
  a. `p.offset()` should be `0`
  b. `p.view_len()` should be `N`
  c. `p.remaining()` should be `N`
2. The method `fn remaining(&self) -> usize` should:
  a. Have `p.remaining() == p.view_len() - p.offset()` at all times
  b. If `p.remaining() == m` before a call to `p.consume(n)` for `m >= n`, a subsequent call should have `p.remaining() == m - n`
  c. If `p.remaining() == m` before a call to `p.set_fit(n)` for `m >= n`, a subsequent call should have `p.remaining() == m`
3. A call `p.consume(n)` should:
  a. Always fail when `nbytes > p.remaining()`, and always succeed when `nbytes <= p.remaining()`
    i. Consequently, `p.consume(0)` must always succeed
  b. Return only `Ok(val)` for `val.len() == n`
4. A call `p.consume_byte()` should:
  a. Be indistinguishable, apart from return value, from `p.consume(1)`
    i. From (2b), `p.remaining() >= 1` should be decremented by 1 following such a call
    ii. From (3a), fail whenever `p.remaining() == 0` and succeed otherwise
  b. Return `Ok(b)` when and only when `p.consume(1)` would have returned `Ok(&[b])`
5. `p.set_fit(m)` should:
  a.  Always fail when `m > p.remaining()`, and always succeed when `m <= p.remaining()`
    i. Consequently, `p.set_fit(0)` must always succeed
  b. Cause a new context window to be created upon success
6. A call `p.enforce_target()` should:
  a. Fail if and only if one of the following apply:
    i. There are no open context-windows
    ii. The innermost target offset has not been reached
    iii. The inner most target offset has somehow been exceeded
  b. Upon success, close the innermost context-window
7. A call `p.test_target()` should:
  a. Return a value equal to the theoretical return value of `p.enforce_target().is_err()`
  b. Have no effect on the context-window state

#### ByteParser

The `ByteParser` type is the primary intended-use implementing type of `Parser`.
As a struct, `ByteParser` consists of an immutable byte-buffer and a mutable
offset-tracker, which also stores context-window state. Consume operations
advance the offset without mutating the buffer itself, and so already-consumed
bytes can theoretically be introspected up until the destructor is called on the
`ByteParser` itself.

#### MemoParser

`MemoParser` is a specialized variant of `ByteParser`, designed primarily for
debugging purposes.  Compared to `ByteParser`, it has a slight overhead in both
memory footprint and performance, but leverages the non-destructive nature of
`ByteParser` consume operations to provide 'backtraces' that indicate which
bytes in the original buffer were consumed as part of the same method call.
These traces are only produced when an error case is encountered.  As its
purpose is mostly to catch implementation bugs, it may be deprecated, and is
otherwise not recommended for performance-sensitive consumers.

#### SliceParser

`SliceParser<'a>` is an alternative model of `Parser` from `ByteParser`. In contrast
to the immutable-buffer, mutable-offset approach of `ByteParser`, `SliceParser<'a>`
maintains a mutable, windowed buffer that is incrementally consumed destructively.
The offset is implicitly always zero, as the buffer is truncated with every consume
operation. It also holds a lifetime parameter, as the internal binary store it uses
consists of a stack of lifetime-annotated slices of the buffer it was created from.

#### TryIntoParser

The `TryIntoParser<P : Parser = ByteParser>` trait is implemented for all types that can be used to construct
a parser-object of type `P` (`ByteParser` when not explicitly listed otherwise).
It has an associated type `Error`, and a single required method, `try_into_parser()`.

While the specific trait bounds may vary, a blanket implementation of `TryIntoParser` is
provided for types satisfying, at the bare minimum, `TryInto<P::Buffer>`, as well as other
possible trait bounds.

There is a slight ambiguity as to whether the `.try_to_parser()` definition for
`String` and `&str` should assume the string is formatted as raw binary, or
encoded as a hex-string. The current model assumes that strings are parsed as
binary, with a feature-flag `"implicit_hexstring"` that causes such types to be
(fallibly) interpreted as hex-strings before conversion into a parser object.

### Target

The trait `Target` is an abstraction over types that store an in-order
traversible sequence of bytes, which, once written, are never subsequently
modified. In this way, it may be thought of as a specialized analogue of
`std::io::Write`.

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

### Builder

The trait `Builder` is an abstraction over types representing fragments of an
intermediate type that can ultimately be finalized and written as a byte-vector,
hex-string, or binary string. It may eventually be deprecated.

### HexString

`HexString` is a newtype around `Vec<u8>` that is used as an intermediate for
serialization, and a pre-processed value for explicit hexadecimal interpretation
of `&str` values we wish to parse via `TryIntoParser::try_into_parser()`. It
exposes a `hex!()` macro that performs conversion from a `String`, `&str`, and
similar types into a `HexString`, which may panic if the conversion cannot be
performed.
