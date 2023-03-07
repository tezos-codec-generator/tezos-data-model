/// Marker trait for byte-oriented buffers with incremental append operations
///
/// In most ways, it is convenient to think of `Target` as an analogous trait to
/// [`std::io::Write`]. The principal difference between the two is the fact
/// that the `push_XXX` methods on `Target` are infallible and total (as opposed
/// to partial) by design; while they return a `usize` value representing the
/// number of bytes written, this is used only for summary book-keeping on the
/// caller side, rather than a feedback mechanism that may indicate failure or
/// partial success, as is the case for `std::io::Write::write`.
///
/// All implementors of `Target` must define these methods as infallible and total.
pub trait Target {
    /// Performs any necessary operations that amortize the cost incurred by
    /// writing a certain number of additional bytes to the end of the `Target`,
    /// over the course of an unknown number of push operations.
    ///
    /// For many implementors, this may simply be a no-op. For underlying structures
    /// with a notion of capacity, such as `Vec<u8>`, this would perform the appropriate
    /// function calls to amortize re-allocation costs by ensuring the capacity is increased
    /// as necessary to accommodate the specified number of extra bytes.
    ///
    /// When writing implementations of this method, note that it may be called with
    /// only partial information as to how many bytes will be written, and additional
    /// writes, as well as other calls to `anticipate`, should be expected to follow.
    fn anticipate(&mut self, extra: usize);

    /// Returns a fresh object of the `Self` type with an initially empty buffer.
    fn create() -> Self;

    /// Appends a single byte to a Target object.
    ///
    /// This method should never panic under normal conditions, and the return value must be `1`.
    fn push_one(&mut self, b: u8) -> usize;

    /// Appends the bytes in a known-length array to a Target object.
    ///
    /// The operational semantics of this method should be indistinguishable from repeated
    /// calls to `push_one` over every element of the array in order, intercalated with
    /// binary addition:
    ///
    /// ```ignore
    /// x.push_many(b"Rust") === x.push_one(b'R') + x.push_one(b'u') + x.push_one(b's') + x.push_one(b't')
    /// ```
    ///
    /// This method should never panic under normal conditions, and the return value must be `N`.
    fn push_many<const N: usize>(&mut self, arr: [u8; N]) -> usize;

    /// Appends the bytes in an arbitrary-length byte-slice to a Target object.
    ///
    /// The operational semantics of this method should be indistinguishable
    /// from repeated calls to `push_one` over every element of the slice in
    /// order, intercalated with binary addition:
    ///
    /// ```ignore
    /// x.push_all(&b"Rust") === x.push_one(b'R') + x.push_one(b'u') + x.push_one(b's') + x.push_one(b't')
    /// ```
    ///
    /// Furthermore, when the slice represents a borrowed reference to an
    /// equivalent array in local scope, the following should hold as well, both
    /// in value and effect:
    ///
    /// ```ignore
    /// x.push_all(&arr) === x.push_many(arr)
    /// ```
    ///
    /// This method should never panic under normal conditions, and the return
    /// value must be the total length of the slice.
    fn push_all(&mut self, buf: &[u8]) -> usize;

    /// Performs any necessary internal stateful operations that 'book-end' a sequence of `push_XXX` operations
    /// to record and preserve the fact that they represent a logical unit.
    ///
    /// More specifically, this method should either be a no-op, or record some indication of the fact that it
    /// was called in between the preceding and subsequent `push_XXX` operations.
    ///
    /// The primary intended use of this method is to allow for the definition of stateful Targets
    /// that facilitate debugging, by partitioning their byte-contents into spans, so that it is possible to
    /// re-associate individual byte-runs with the context of what constituent value they might represent.
    ///
    /// By definition, the effect of this function must not have influence on the actual contents of the buffer
    /// beyond internal division or segmentation, and so a default no-op implementation is provided, as few, if any,
    /// implementors will have need to override this.
    #[inline(always)]
    fn resolve(&mut self) {}

    /// Perform the associated `Target::resolve` call on the argument expression and return `0usize`
    ///
    /// # Note
    ///
    /// This method has a default implementation that should only be overridden with care.
    /// In particular, no matter how it is implemented, the return value should always be `0`.
    #[inline]
    fn resolve_zero(&mut self) -> usize {
        self.resolve();
        0
    }
}

#[macro_export]
macro_rules! resolve_zero {
    ( $buf:expr ) => {{
        $crate::conv::target::Target::resolve($buf);
        0
    }};
}

/// Useful alias for `std::io::Sink` that is used to count the number of
/// bytes required to serialize an arbitrary-typed object, without
/// performing any memory operations.
pub type ByteCounter = std::io::Sink;

impl Target for ByteCounter {
    #[inline(always)]
    fn anticipate(&mut self, _: usize) {}

    #[inline]
    fn create() -> Self {
        std::io::sink()
    }

    #[inline(always)]
    fn push_one(&mut self, _: u8) -> usize {
        1
    }

    #[inline(always)]
    fn push_many<const N: usize>(&mut self, _: [u8; N]) -> usize {
        N
    }

    #[inline(always)]
    fn push_all(&mut self, buf: &[u8]) -> usize {
        buf.len()
    }
}

impl Target for Vec<u8> {
    #[inline]
    fn anticipate(&mut self, extra: usize) {
        self.reserve(extra)
    }

    #[inline]
    #[must_use]
    fn create() -> Self {
        Self::new()
    }

    #[inline]
    fn push_one(&mut self, b: u8) -> usize {
        self.push(b);
        1
    }

    #[inline]
    fn push_many<const N: usize>(&mut self, arr: [u8; N]) -> usize {
        self.extend(&arr);
        N
    }

    #[inline]
    fn push_all(&mut self, buf: &[u8]) -> usize {
        self.extend_from_slice(buf);
        buf.len()
    }
}
/*
impl<T: std::io::Write> Target for T {
    fn push_one(&mut self, b: u8) -> usize {
        self.write(&[b])
    }

    fn push_many<const N: usize>(&mut self, arr: [u8; N]) -> usize {
        self.write(&arr)
    }

    fn push_all(&mut self, buf: &[u8]) -> usize {
        self.write(buf)
    }
}
*/
