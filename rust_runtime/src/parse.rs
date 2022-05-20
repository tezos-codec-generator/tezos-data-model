pub mod error;

pub mod hexstring;

pub mod bytes {
    use super::hexstring::HexString;

    /// Newtype around an explicitly lifetime-annotated immutable slice of type `&[u8]`
    #[derive(Clone, Copy)]
    pub struct ByteSlice<'a>(&'a [u8]);

    /// Newtype around a vector of type `Vec<u8>`
    #[derive(Clone)]
    pub struct OwnedBytes(Vec<u8>);

    impl<'a> From<&'a [u8]> for ByteSlice<'a> {
        fn from(bytes: &'a [u8]) -> Self {
            Self(bytes)
        }
    }

    impl From<&[u8]> for OwnedBytes {
        fn from(bytes: &[u8]) -> Self {
            Self(bytes.to_owned())
        }
    }

    impl From<Vec<u8>> for OwnedBytes {
        fn from(bytes: Vec<u8>) -> Self {
            Self(bytes)
        }
    }

    impl<const N: usize> From<[u8; N]> for OwnedBytes {
        fn from(bytes: [u8; N]) -> Self {
            Self(bytes.to_vec())
        }
    }

    impl From<HexString> for OwnedBytes {
        fn from(hex: HexString) -> Self {
            Self(hex.to_vec())
        }
    }

    impl From<&str> for OwnedBytes {
        fn from(s: &str) -> Self {
            // hex!(s).into()
            Self(s.as_bytes().to_owned())
        }
    }

    impl<'a> ByteSlice<'a> {
        /// Extracts the first `N` indices of a `ByteSlice` and return them
        /// as a slice, along with the remainder as a `ByteSlice`
        ///
        /// This function is only `unsafe` because it does not itself perrform
        /// any slice-length bound-checking and will therefore panic as normal
        /// when the number of indices to take exceeds the number of indices
        /// in the slice itself.
        pub unsafe fn take(&self, len: usize) -> (&'a [u8], Self) {
            (&self.0[..len], Self(&self.0[len..]))
        }

        /// Equivalent to `ByteSlice::take`, except the first element of the
        /// tuple is itself a `ByteSlice`, rather than a raw `&'a [u8]`.
        pub unsafe fn split(&self, len: usize) -> (Self, Self) {
            (Self(&self.0[..len]), Self(&self.0[len..]))
        }

        /// Special version of `ByteSlice::take` that is optimized for only taking
        /// one byte (at index 0). Other than returning a Copied `u8` rather than
        /// a singleton slice of type `&'a [u8]`, `self.pop()` is semantically equivalent
        /// to `self.take(1)`
        pub unsafe fn pop(&self) -> (u8, Self) {
            (self.0[0], Self(&self.0[1..]))
        }

        /// Returns the number of bytes in a ByteSlice.
        pub fn len(&self) -> usize {
            self.0.len()
        }
    }

    impl OwnedBytes {
        /// Borrows a range of bytes starting at index `ix`, of length `len`.
        ///
        /// This function is marked as `unsafe` to ensure that the caller is certain
        /// that the attempted slice access will not violate the bounds of the vector
        /// wrapped inside the receiver. If this guarantee is not made, this function
        /// will panic as usual, but does not itself perform any bounds validation beyond
        /// what Rust itself performs when attempting to borrow a range of indices of
        /// a vector as a slice.
        pub unsafe fn get_slice(&self, ix: usize, len: usize) -> &[u8] {
            &self.0[ix..ix + len]
        }

        /// Specialized variant of `get_slice` optimized for the case in which
        /// only one byte is desired, returning an owned byte (as `u8`) rather than
        /// a slice of bytes.
        pub unsafe fn get_word(&self, ix: usize) -> u8 {
            self.0[ix]
        }

        /// Returns the length of the vector enclosed by an OwnedBytes value.
        pub fn len(&self) -> usize {
            self.0.len()
        }
    }
}

pub mod byteparser {
    use crate::internal::{BoundAwareMarker, ContextOffset, Marker, SplitVec, Stack};
    use crate::parse::error::InternalErrorKind;

    use super::bytes::{ByteSlice, OwnedBytes};
    use super::error::{ParseError, TagError};
    use std::convert::{TryFrom, TryInto};
    use std::ops::Deref;

    pub type ParseResult<T> = Result<T, ParseError>;

    /**
     # Parser

      This trait is an abstraction over types respresenting a stateful
      parse-object, with default implementations for a variety of monomorphic
      `get_*` functions, as well as query operations on the internal state,
      and state-mutational functions that operate on *context-windows*.

     ## Model

     While the implementing types are largely free to define their own
     operational semantics for the required methods of this function, the
     intensional semantics are as follows:

     * The Parser-object is constructed over an immutable byte-buffer.
     * All parsing is done in a non-backtracking, zero-lookahead fashion; a byte in the buffer
       can only be viewed by consuming it, and only after all preceding indices in the buffer
       have been consumed; after a byte is consumed, it cannot be consumed again.
     * A *context-window*, or a bounded contiguous view of a section of the buffer,
       may be constructed. While a context-window exists, any bytes beyond its upper bound
       are protected and cannot be consumed by any Parser method until that
       context window is lifted. A context-window can only be lifted by calling
       [enforce_target] when all bytes within the window have been consumed.

    ## Context-Windows

    In order to facilitate bounds-setting and bounds-checking for dynamically sized elements with length prefixes,
    `Parser` uses a model of *context windows*, which are conceptually (though not necessarily implementationally) a stack
    of target offsets, which may in fact be hard lower bounds on remainding-buffer-length in the case of slice-based parsers, or fixed values
    of the mutating parse-head for buffer-based implementations such as [ByteParser].

    The following properties should be respected by each implementation of the `Parser` trait:

    * A fresh `p : impl Parser` object should have `p.offset() == 0` and `p.len()` equal to the length of the parse-buffer
    * `self.len() - self.offset()` is the largest possible `n` for which `self.consume(n)` returns an `Ok(_)` value, which should also be the largest possible `n` for which `self.set_fit(n)` succeeds. Both should fail for any greater values of `n`, either through `Err(_)` returns or panics.
    * The value of `self.len() - self.offset()` before and after a call to `self.consume(n)` should represent a decrease by `n` if the consume call is an `Ok(_)` value, or remain unchanged if it is an `Err(_)` value. Only one of `self.len()` and `self.offset()` should change in this fashion.
    * `self.set_fit(m)` should fail whenever `self.len() < m + self.offset()`, and succeed otherwise
    * Immediately after a successful call of `self.set_fit(n)`, `self.len() == n + self.offset()` should hold.
    * `self.test_target()` should return `true` if and only if `self.offset() == self.len()` holds with at least one context window present
    * `self.enforce_target()` should remove the most recently set target if `self.test_target()` would return true, and panic otherwise

    */
    pub trait Parser: Iterator<Item = u8> {
        /** Computes the length of the current view of the Parser's buffer.
         *
         * Decrements in the shrinking-slice model, and remains invariant modulo context-window
         * manipulation in the buffer-with-offset model
         */
        fn len(&self) -> usize;

        /** Computes the current value of the offset into the Parser's buffer.
         *
         * This should either be invariant, or increase by the number of bytes consumed
         * by any method that returns bytes from the buffer.
         */
        fn offset(&self) -> usize;

        fn remainder(&self) -> usize {
            self.len() - self.offset()
        }

        /** Consumes and returns a slice of length `nbytes` starting from the current offset of the buffer.
         */
        fn consume(&mut self, nbytes: usize) -> ParseResult<&[u8]>;

        fn set_fit(&mut self, n: usize);

        fn test_target(&mut self) -> bool;

        fn enforce_target(&mut self);

        fn consume_arr<const N: usize>(&mut self) -> ParseResult<[u8; N]> {
            let ret = self.consume(N);
            match ret {
                Err(e) => Err(e),
                Ok(bytes) => bytes.try_into().or(Err(ParseError::InternalError(
                    InternalErrorKind::SliceCoerceFailure,
                ))),
            }
        }

        fn get_u8(&mut self) -> ParseResult<u8> {
            match self.next() {
                Some(byte) => Ok(byte),
                None => Err(ParseError::BufferOverflow {
                    buflen: self.len(),
                    requested: 1,
                    offset: self.offset(),
                }),
            }
        }

        fn get_i8(&mut self) -> ParseResult<i8> {
            match self.next() {
                Some(byte) => Ok(byte as i8),
                None => Err(ParseError::BufferOverflow {
                    buflen: self.len(),
                    requested: 1,
                    offset: self.offset(),
                }),
            }
        }

        fn get_u16(&mut self) -> ParseResult<u16> {
            self.consume_arr::<2>().map(u16::from_be_bytes)
        }

        fn get_i16(&mut self) -> ParseResult<i16> {
            self.consume_arr::<2>().map(i16::from_be_bytes)
        }

        fn get_u32(&mut self) -> ParseResult<u32> {
            self.consume_arr::<4>().map(u32::from_be_bytes)
        }

        fn get_i32(&mut self) -> ParseResult<i32> {
            self.consume_arr::<4>().map(i32::from_be_bytes)
        }

        fn get_u64(&mut self) -> ParseResult<u64> {
            self.consume_arr::<8>().map(u64::from_be_bytes)
        }

        fn get_i64(&mut self) -> ParseResult<i64> {
            self.consume_arr::<8>().map(i64::from_be_bytes)
        }

        fn get_bool(&mut self) -> ParseResult<bool> {
            match self.next() {
                Some(byte) => match byte {
                    0xff => Ok(true),
                    0x00 => Ok(false),
                    _ => Err(ParseError::InvalidBoolean(byte)),
                },
                None => Err(ParseError::BufferOverflow {
                    buflen: self.len(),
                    requested: 1,
                    offset: self.offset(),
                }),
            }
        }

        fn get_tagword<T, U>(&mut self, valid: &[U]) -> ParseResult<U>
        where
            U: super::error::TagType + crate::conv::Decode,
            Self: Sized,
        {
            if let [] = valid {
                return Err(ParseError::InternalError(InternalErrorKind::NoValidTags));
            }
            let actual: U = crate::conv::Decode::parse(self)?;
            if valid.contains(&actual) {
                Ok(actual)
            } else {
                Err(ParseError::InvalidTag(
                    TagError::new(
                        actual,
                        Some(std::any::type_name::<T>().to_owned()),
                        Some(valid.to_vec()),
                    )
                    .into(),
                ))
            }
        }

        fn get_dynamic(&mut self, nbytes: usize) -> ParseResult<Vec<u8>> {
            self.consume(nbytes).map(Vec::from)
        }

        fn get_fixed<const N: usize>(&mut self) -> ParseResult<[u8; N]> {
            self.consume_arr::<N>()
        }

        fn get_self_terminating<F>(&mut self, is_terminal: F) -> ParseResult<Vec<u8>>
        where
            F: Fn(u8) -> bool,
        {
            let mut ret: Vec<u8> = Vec::with_capacity(self.len() - self.offset());
            loop {
                if let Some(byte) = self.next() {
                    ret.push(byte);
                    if is_terminal(byte) {
                        break Ok(ret);
                    }
                } else {
                    break Err(ParseError::NonTerminating(ret));
                }
            }
        }
    }

    pub struct ByteParser {
        buffer: OwnedBytes,
        offset: ContextOffset,
    }

    impl ByteParser {
        /// Convert any type that can be potentially coerced into an `OwnedBytes` value into
        /// a ByteParser over said buffer, with an empty stack of context windows and an offset
        /// starting at index `0`.
        pub fn parse<T>(input: T) -> ParseResult<Self>
        where
            OwnedBytes: TryFrom<T>,
            <T as TryInto<OwnedBytes>>::Error: Into<ParseError>,
        {
            match OwnedBytes::try_from(input) {
                Ok(buffer) => {
                    let offset = ContextOffset::new(buffer.len());
                    Ok(Self { buffer, offset })
                }
                Err(err) => Err(err.into()),
            }
        }
    }

    impl Iterator for ByteParser {
        type Item = u8;

        fn next(&mut self) -> Option<Self::Item> {
            let (ix, adv) = self.offset.advance(1);
            if adv {
                Some(unsafe { self.buffer.get_word(ix) })
            } else {
                None
            }
        }
    }

    impl Parser for ByteParser {
        fn len(&self) -> usize {
            self.offset.lim()
        }

        fn offset(&self) -> usize {
            self.offset.get()
        }

        fn set_fit(&mut self, n: usize) {
            self.offset.set_fit(n)
        }

        fn test_target(&mut self) -> bool {
            self.offset.test_target()
        }

        fn enforce_target(&mut self) {
            self.offset.enforce_target()
        }

        fn consume(&mut self, nbytes: usize) -> ParseResult<&[u8]> {
            let (ix, adv) = self.offset.advance(nbytes);
            if adv {
                Ok(unsafe { self.buffer.get_slice(ix, nbytes) })
            } else {
                Err(ParseError::BufferOverflow {
                    offset: ix,
                    requested: nbytes,
                    buflen: self.buffer.len(),
                })
            }
        }
    }

    pub struct MemoParser {
        buffer: OwnedBytes,
        offset: ContextOffset,
        munches: Vec<usize>,
    }

    impl MemoParser {
        /// Convert any type that can be potentially coerced into an `OwnedBytes` value into
        /// a ByteParser over said buffer, with an empty stack of context windows and an offset
        /// starting at index `0`.
        pub fn parse<T>(input: T) -> ParseResult<Self>
        where
            OwnedBytes: TryFrom<T>,
            <T as TryInto<OwnedBytes>>::Error: Into<ParseError>,
        {
            match OwnedBytes::try_from(input) {
                Ok(buffer) => {
                    let offset = ContextOffset::new(buffer.len());
                    let munches = Vec::new();
                    Ok(Self {
                        buffer,
                        offset,
                        munches,
                    })
                }
                Err(err) => Err(err.into()),
            }
        }
    }

    impl Iterator for MemoParser {
        type Item = u8;

        fn next(&mut self) -> Option<Self::Item> {
            let (ix, adv) = self.offset.advance(1);
            if adv {
                self.munches.push(1);
                Some(unsafe { self.buffer.get_word(ix) })
            } else {
                None
            }
        }
    }

    impl Parser for MemoParser {
        fn len(&self) -> usize {
            self.offset.lim()
        }

        fn offset(&self) -> usize {
            self.offset.get()
        }

        fn set_fit(&mut self, n: usize) {
            self.offset.set_fit(n)
        }

        fn test_target(&mut self) -> bool {
            self.offset.test_target()
        }

        fn enforce_target(&mut self) {
            self.offset.enforce_target()
        }

        fn consume(&mut self, nbytes: usize) -> ParseResult<&[u8]> {
            let (ix, adv) = self.offset.advance(nbytes);
            if adv {
                self.munches.push(nbytes);
                Ok(unsafe { self.buffer.get_slice(ix, nbytes) })
            } else {
                let offset = ix;
                let mut splits = SplitVec::new();
                let mut ix: usize = 0;
                for &len in self.munches.iter() {
                    unsafe {
                        let tmp: &[u8] = self.buffer.get_slice(ix, len);
                        splits.extend_current(tmp.iter().copied());
                        splits.split();
                    }
                    ix += len;
                }
                eprintln!("{}", splits);

                Err(ParseError::BufferOverflow {
                    offset,
                    requested: nbytes,
                    buflen: self.buffer.len(),
                })
            }
        }
    }

    pub struct SliceParser<'a>(Vec<ByteSlice<'a>>);

    impl<'a> SliceParser<'a> {
        /// Convert any type that can be potentially coerced into a `ByteSlice` value into
        /// a SliceParser over said slice.
        ///
        /// If any error is encountered during conversion into the `ByteSlice`, this function
        /// will panic with that error as its displayed exception context.
        pub fn parse<T>(input: T) -> ParseResult<Self>
        where
            ByteSlice<'a>: TryFrom<T>,
            <T as TryInto<ByteSlice<'a>>>::Error: Into<ParseError>,
        {
            match ByteSlice::<'a>::try_from(input) {
                Ok(slice) => Ok(Self(vec![slice])),
                Err(err) => Err(err.into()),
            }
        }
    }

    impl<'a> Iterator for SliceParser<'a> {
        type Item = u8;

        fn next(&mut self) -> Option<Self::Item> {
            match Stack::peek_mut(&mut self.0) {
                None => None,
                Some(frame) => {
                    if frame.len() > 0 {
                        unsafe {
                            let (ret, temp) = frame.take(1);
                            *frame = temp;
                            debug_assert!(ret.len() == 1);
                            Some(ret[0])
                        }
                    } else {
                        None
                    }
                }
            }
        }
    }

    impl<'a> Parser for SliceParser<'a> {
        fn len(&self) -> usize {
            match self.0.peek() {
                Some(bs) => bs.len(),
                None => 0,
            }
        }

        fn offset(&self) -> usize {
            0
        }

        fn consume(&mut self, nbytes: usize) -> ParseResult<&[u8]> {
            match <Vec<_> as Stack>::peek_mut(&mut self.0) {
                None => Err(ParseError::BufferOverflow {
                    buflen: 0,
                    requested: nbytes,
                    offset: 0,
                }),
                Some(frame) => {
                    if frame.len() >= nbytes {
                        unsafe {
                            let (ret, temp) = frame.take(nbytes);
                            *frame = temp;
                            Ok(ret)
                        }
                    } else {
                        Err(ParseError::BufferOverflow {
                            buflen: frame.len(),
                            requested: nbytes,
                            offset: 0,
                        })
                    }
                }
            }
        }

        fn set_fit(&mut self, n: usize) {
            match self.0.peek_mut() {
                None if n == 0 => (),
                None => panic!(
                    "SliceParser::set_fit: Cannot reserve {} bytes of empty buffer",
                    n
                ),
                Some(frame) => {
                    if frame.len() >= n {
                        unsafe {
                            let (novel, rem) = frame.split(n);
                            *frame = rem;
                            self.0.push(novel);
                        }
                    } else {
                        panic!(
                            "Cannot set fit of {} bytes when current frame contains {} bytes",
                            n,
                            frame.len()
                        );
                    }
                }
            }
        }

        fn test_target(&mut self) -> bool {
            match self.0.peek() {
                None => false,
                Some(frame) => frame.len() == 0,
            }
        }

        fn enforce_target(&mut self) {
            assert_eq!(self.0.pop().expect("No target to enforce!").len(), 0);
        }
    }

    pub trait ToParser<P: Parser = ByteParser> {
        fn into_parser(self) -> ParseResult<P>;

        fn to_parser(self) -> P
        where
            Self: Sized,
        {
            self.into_parser()
                .expect("ToParser::to_parser: encountered error in self.into_parser")
        }
    }

    impl ToParser<ByteParser> for ByteParser {
        fn into_parser(self) -> ParseResult<Self> {
            Ok(self)
        }
    }

    impl<'a> ToParser<SliceParser<'a>> for SliceParser<'a> {
        fn into_parser(self) -> ParseResult<Self> {
            Ok(self)
        }
    }

    impl<T> ToParser<ByteParser> for T
    where
        OwnedBytes: TryFrom<T>,
        <T as TryInto<OwnedBytes>>::Error: std::fmt::Display + Into<ParseError>,
    {
        fn into_parser(self) -> ParseResult<ByteParser> {
            ByteParser::parse(self)
        }
    }

    impl<T> ToParser<MemoParser> for T
    where
        OwnedBytes: TryFrom<T>,
        <T as TryInto<OwnedBytes>>::Error: std::fmt::Display + Into<ParseError>,
    {
        fn into_parser(self) -> ParseResult<MemoParser> {
            MemoParser::parse(self)
        }
    }


    impl<'a, T> ToParser<SliceParser<'a>> for T
    where
        ByteSlice<'a>: TryFrom<T>,
        <T as TryInto<ByteSlice<'a>>>::Error: Into<ParseError>,
    {
        fn into_parser(self) -> ParseResult<SliceParser<'a>> {
            SliceParser::parse(self)
        }
    }

    impl<const N: usize> ToParser for &[u8; N] {
        fn into_parser(self) -> ParseResult<ByteParser> {
            ByteParser::parse(self.to_vec())
        }
    }

    impl ToParser for String {
        fn into_parser(self) -> ParseResult<ByteParser> {
            ByteParser::parse(self.deref())
        }
    }
}
