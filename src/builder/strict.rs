//! Builder type implemented as a newtype around `Vec<u8>`
//!
//! StrictBuilder is named after Haskell's `Data.ByteString.Strict`.
//! There used to also be a `LazyBuilder`, but it eventually removed
//! as it was not implemented efficiently enough to justify its
//! continued inclusion.

use std::borrow::Borrow;

use crate::conv::target::Target;

/// Newtype around `Vec<u8>` to use as Builder
///
/// Unless otherwise indicated,  Most of the methods on `StrictBuilder` are implemented directly on the
/// underlying `Vec<u8>` and may not be explicitly documented due to how trivial
/// they are.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
#[repr(transparent)]
pub struct StrictBuilder(Vec<u8>);

impl Borrow<[u8]> for StrictBuilder {
    fn borrow(&self) -> &[u8] {
        self.0.borrow()
    }
}

impl From<StrictBuilder> for Vec<u8> {
    fn from(val: StrictBuilder) -> Self {
        val.0
    }
}

impl From<Vec<u8>> for StrictBuilder {
    fn from(buf: Vec<u8>) -> StrictBuilder {
        StrictBuilder(buf)
    }
}

impl From<&[u8]> for StrictBuilder {
    fn from(buf: &[u8]) -> StrictBuilder {
        StrictBuilder(buf.into())
    }
}

impl std::io::Write for StrictBuilder {
    /// Calls `<Vec<u8> as Write>::write` on the inner vector
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.write(buf)
    }

    /// Calls `<Vec<u8> as Write>::flush` on the inner vector
    fn flush(&mut self) -> std::io::Result<()> {
        self.0.flush()
    }
}

impl Target for StrictBuilder {
    /// Calls `<Vec<u8> as Target>::anticipate` on the inner vector
    fn anticipate(&mut self, extra: usize) {
        self.0.anticipate(extra)
    }

    /// Constructs a `StrictBuilder` via `<Vec<u8> as Target>::create`
    fn create() -> Self {
        Self(Vec::create())
    }

    /// Calls `<Vec<u8> as Target>::push_one` on the inner vector.
    fn push_one(&mut self, b: u8) -> usize {
        self.0.push_one(b)
    }

    /// Calls `<Vec<u8> as Target>::push_many` on the inner vector
    fn push_many<const N: usize>(&mut self, arr: [u8; N]) -> usize {
        self.0.push_many(arr)
    }

    /// Calls `<Vec<u8> as Target>::push_all` on the inner vector.
    fn push_all(&mut self, buf: &[u8]) -> usize {
        self.0.push_all(buf)
    }

    /// Calls `<Vec<u8> as Target>::resolve` on the inner vector.
    fn resolve(&mut self) {
        self.0.resolve()
    }
}

impl super::Builder for StrictBuilder {
    /// `StrictBuilder` does not have any metadata or structure
    /// beyond being a vector, and so it is considered its own
    /// Segment type.
    type Segment = Self;

    /// In order to distinguish between finalized and non-finalized
    /// `StrictBuilders`, `Final := Vec<u8>` is used over `Final := Self`
    type Final = Vec<u8>;

    /// Returns the argument `seg`
    fn promote(seg: Self::Segment) -> Self {
        seg
    }

    /// Creates a `StrictBuilder` containing a vector that holds the single byte `b`.
    fn word(b: u8) -> Self {
        vec![b].into()
    }

    /// Creates a `StrictBuilder` containing a vector that holds the contents of array `b`.
    fn words<const N: usize>(arr: [u8; N]) -> Self {
        arr.to_vec().into()
    }

    /// Finalizes a `StrictBuilder` by destructing it
    fn finalize(self) -> Self::Final {
        self.0
    }

    /// Returns the number of bytes contained in `self`
    fn len(&self) -> usize {
        Vec::len(&self.0)
    }
}
