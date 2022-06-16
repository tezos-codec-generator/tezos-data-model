//! Builder type that preserves grouping of written bytes
//!
//! This module defines the type `MemoBuilder`, which is one of the implementing
//! types of the `Builder` trait defined in the parent module.
//!
//! It is effectively equivalent to `StrictBuilder`, the default implementor of
//! `Builder` for most purposes, except that it preserves metadata as to which
//! bytes were written in a single method call, and which were written across
//! different method calls.
//!
//! Recording and maintaining this added information imposes an overhead in both
//! memory usage and performance. Its intended use is to aid in debugging and
//! manual inspection, as it may be difficult to determine what bytes in a
//! serialized bytestring belong to what segment of a complex codec type.

use std::fmt::Write;

use crate::{conv::target::Target, internal::SplitVec, util::write_all_hex};

use super::Builder;

/// Builder type that additionally records how written bytes were grouped
///
/// As compared to [`StrictBuilder`](../strict/struct.StrictBuilder.html),
/// this type is less compact and has a higher performance cost for most
/// methods. Unless segmentation metadata is desired, it is recommended
/// to use `StrictBuilder` over `MemoBuilder` for performance reasons.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Default, Hash)]
#[repr(transparent)]
pub struct MemoBuilder {
    segs: SplitVec<u8>,
}

impl MemoBuilder {
    /// Constructs a new, empty MemoBuilder
    #[must_use]
    #[inline]
    pub fn new() -> Self {
        Self { segs: SplitVec::new() }
    }
}

impl std::fmt::Debug for MemoBuilder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemoBuilder")
            .field("segs", &self.segs)
            .finish()
    }
}

impl std::fmt::Display for MemoBuilder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self.segs)
    }
}


impl From<MemoBuilder> for Vec<u8> {
    fn from(val: MemoBuilder) -> Self {
        val.segs.into_inner()
    }
}

impl From<Vec<u8>> for MemoBuilder {
    fn from(buf: Vec<u8>) -> Self {
        Self {
            segs: SplitVec::from_vec(buf),
        }
    }
}

impl From<&[u8]> for MemoBuilder {
    fn from(buf: &[u8]) -> MemoBuilder {
        Self::from(<&[u8] as Into<Vec<u8>>>::into(buf))
    }
}

/// Utility type for processing finalized `MemoBuilder` objects
///
/// A similar internal type is used within `MemoBuilder` objects,
/// but unlike `MemoBuffer`, that type is optimized for writes,
/// which is unnecessary once the `MemoBuilder` is final.
///
/// In addition, the actual implementations may at some point
/// diverge, so this similarity may be short-lived.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemoBuffer {
    buf: Vec<u8>,
    lens: Vec<usize>,
}

impl From<SplitVec<u8>> for MemoBuffer {
    fn from(val: SplitVec<u8>) -> Self {
        let (buf, lens) = val.into_parts();
        Self { buf, lens }
    }
}

impl From<MemoBuffer> for Vec<u8> {
    fn from(val: MemoBuffer) -> Self {
        val.buf
    }
}

impl std::fmt::Debug for MemoBuffer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemoBuffer")
            .field("buf", &self.buf)
            .field("lens", &self.lens)
            .finish()
    }
}

impl std::fmt::Display for MemoBuffer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buf: &[u8] = &self.buf[..];
        write!(f, "[|")?;
        for &l in self.lens.iter() {
            write_all_hex(&buf[..l], f)?;
            f.write_char('|')?;
            buf = &buf[l..];
        }
        f.write_char(']')
    }
}

impl std::io::Write for MemoBuilder {
    /// Appends the contents of a `&[u8]` to the internal byte-store
    /// of a `MemoBuilder`, without introducing any new segmentation.
    ///
    /// Always writes the entirety of `buf` and returns `Ok(N)` for `N := buf.len()`
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.segs.extend_current_from_slice(buf);
        Ok(buf.len())
    }

    /// Signals that the bytes written since the last `flush` call
    /// belong to a single logical group, and marks that group
    /// as having terminated.
    ///
    /// This method does not actually 'flush' previous write-data,
    /// but it performs memory operations.
    ///
    /// Always returns `Ok(())`
    fn flush(&mut self) -> std::io::Result<()> {
        self.segs.split();
        Ok(())
    }
}

impl Target for MemoBuilder {
    #[inline]
    /// Pre-allocates space for at least `n` more bytes to be written.
    ///
    /// As the segmentation of these `n` bytes cannot be predicted,
    /// some re-allocations may still occur if enough segments are
    /// added.
    fn anticipate(&mut self, n: usize) {
        self.segs.buffer.reserve(n)
    }

    /// Constructs a new, empty `MemoBuilder`
    #[inline]
    fn create() -> Self {
        Self {
            segs: SplitVec::new(),
        }
    }

    /// Pushes a single byte into `self` and returns `1`
    #[inline]
    fn push_one(&mut self, b: u8) -> usize {
        self.segs.push_current(b);
        1
    }

    /// Pushes the contents of a byte-array into `self` and returns its length
    #[inline]
    fn push_many<const N: usize>(&mut self, arr: [u8; N]) -> usize {
        self.segs.extend_current_from_slice(&arr);
        N
    }

    /// Pushes the contents of a byte-slice into `self` and returns its length
    #[inline]
    fn push_all(&mut self, buf: &[u8]) -> usize {
        let l = buf.len();
        self.segs.extend_current_from_slice(buf);
        l
    }

    /// Finalizes the currently active segment without explicitly creating
    /// a new empty segment.
    ///
    /// Has no effect when preceded by another `resolve` call (i.e. this method is idempotent).
    ///
    /// A new empty segment is implicitly created by calling any `push_XXX`
    /// operation after `resolve`.
    fn resolve(&mut self) {
        self.segs.split();
    }
}

impl Builder for MemoBuilder {
    type Segment = Vec<u8>;

    type Final = MemoBuffer;

    /// Promotes a `Vec<u8>` into a `MemoBuilder` containing its bytes
    /// as a single segment
    #[inline]
    #[must_use]
    fn promote(seg: Self::Segment) -> Self {
        Self {
            segs: SplitVec::from_vec(seg),
        }
    }

    /// Creates a `MemoBuilder` fragment containing a single byte
    #[inline]
    #[must_use]
    fn word(b: u8) -> Self {
        vec![b].into()
    }

    /// Creates a `MemoBuilder` fragment containing a fixed number of bytes
    #[inline]
    #[must_use]
    fn words<const N: usize>(b: [u8; N]) -> Self {
        b.to_vec().into()
    }

    /// Converts a `MemoBuilder` into a `MemoBuffer`, which cannot be appended
    /// to any further, and is optimized for reading rather than writing.
    #[inline]
    #[must_use]
    fn finalize(self) -> Self::Final {
        self.segs.into()
    }

    /// Returns the number of bytes contained in `self`
    #[inline]
    #[must_use]
    fn len(&self) -> usize {
        self.segs.len()
    }
}
