//! Vectors with virtual segmentation
//!
//! This module contains the utility type [`SplitVec<T>`], which
//! is logically a sub-type of `Vec<T>` that is useful for debugging
//! purposes, in that it is virtually segmented into adjacent
//! but distinct contiguous spans of elements, which can be presented
//! in groups until this metadata is willfully discarded.
//!
//! It is used primarily for the purposes of the debugging-oriented
//! types [`MemoBuilder`](../../builder/memo/struct.MemoBuilder.html)
//! and [`MemoParser`](../../parse/memoparser/struct.MemoParser.html)
//! as well as in the generic end-of-lifetime cleanup logic used
//! generically for implementors of the [`Parser`](../../parse/trait.Parser.html)
//! trait.

use std::ops::AddAssign;

mod spanbuffer {
    use std::ops::AddAssign;

    /// Specialized `Vec<usize>` derivative for modeling the span-buffer of a [`SplitVec<T>`]
    ///
    /// # Model and Terminology
    ///
    /// A `SplitVec<T>` consists of a `Vec<T>`, its 'value-buffer', as well as a `SpanBuffer`
    /// object, which records the lengths for each 'span' of values, in order. In other words,
    /// a `SpanBuffer` contains the segmentation information of a `SplitVec<T>`.
    ///
    /// A `SpanBuffer` consists of a heap-allocated buffer of 'frozen' span-lengths, which may
    /// also be referred to individually as 'finalized', or in aggregate as 'stable'.
    /// This internal buffer starts out empty, and only changes when an unfrozen span-length,
    /// also known as the 'active' or 'current' span-length, is frozen, at which point it is
    /// appended to this buffer.
    ///
    /// At any point, at most one span-length can be unfrozen. This is because a `SplitVec<T>`
    /// is an append-only buffer, and so a span-length, once frozen, will never change;
    /// the only way that new elements are inserted into a `SplitVec<T>` is by appending them,
    /// which implicitly extends either the extant, or a novel span. In the latter case, the
    /// pre-existing unfrozen span-length is finalized as soon as the subsequent span is
    /// initialized.
    ///
    /// The 'active' span-length starts out uninitialized, that is, holding no value (this is logically
    /// distinct from holding the value `0`). In this state,
    /// the [`flush`][flush] method, which is responsible for freezing the active span-length and appending
    /// it to the internal buffer, will have no effect.
    ///
    /// The method [`active_mut`][activemut], which returns a mutable reference to the active span-length
    /// as `&mut usize`, will initialize it to `0` if it was previously uninitialized. This initialazation
    /// cannot be undone, and a 0-valued active span-length **will** be appended to the internal buffer
    /// if frozen.
    ///
    /// It is possible, though not advised, to [`unfreeze`] the final element of the internal buffer,
    /// which can only be done safely when the internal buffer is not empty, and the current active
    /// span-length is uninitialized. If these conditions are both guaranteed in the calling context,
    /// the unsafe version [`unfreeze_unchecked`] may be used instead.
    ///
    /// [flush]: ./struct.SpanBUffer.html#method.flush
    /// [activemut]: ./struct.SpanBuffer.html#method.active_mut
    #[derive(Clone, PartialOrd, PartialEq, Ord, Default, Eq, Hash)]
    pub struct SpanBuffer {
        pub(crate) stable: Vec<usize>,
        pub(crate) active: Option<usize>,
        pub(crate) _cache: usize,
    }

    impl SpanBuffer {
        /// Creates a new SpanBuffer object.
        ///
        /// The returned value contains no spans.
        ///
        /// # Examples
        ///
        /// ```ignore
        /// # use rust_runtime::internal::splitvec::SpanBuffer;
        /// let x = SpanBuffer::new();
        /// assert!(x.is_empty());
        /// ```
        #[must_use]
        #[inline(always)]
        pub fn new() -> Self {
            Self {
                stable: Vec::new(),
                active: None,
                _cache: 0,
            }
        }

        /// Returns a mutable reference to the active span-length
        ///
        /// If the active span-length is uninitialized, this method
        /// causes it to be initialized to 0.
        ///
        /// ```ignore
        /// # use ::rust_runtime::internal::splitvec::SpanBuffer;
        /// let mut s = SpanBuffer::new();
        /// let x : &mut usize = s.active_mut();
        /// assert_eq!(*x, 0usize);
        /// *x = 10;
        /// s.flush();
        /// let y : &mut usize = s.active_mut();
        /// assert_eq!(*y, 0usize);
        /// ```
        #[inline(always)]
        pub fn active_mut(&mut self) -> &mut usize {
            self.active.get_or_insert(0)
        }

        /// Finalize the active value and append it to the span-buffer
        ///
        /// After calling this function, calls to `active_mut` will
        /// initialize a new active span-length to `0` and continue to
        /// point to said value until `flush` is called again.
        ///
        /// Calling this function will have no effect if the
        #[inline]
        pub fn flush(&mut self) {
            if let Some(last) = self.active.take() {
                self.stable.push(last);
                self._cache += last;
            }
        }

        /// Finalize  `force_flush`: variant of the [`flush`] function that
        /// always pushes a finalized value, defaulting to 0 if
        /// the active span-length is uninitialized.
        ///
        /// Unlike [`flush`], this function is not idempotent.
        #[inline]
        pub fn flush_force(&mut self) {
            let frozen = self.active.take().unwrap_or(0);
            self.stable.push(frozen);
            self._cache += frozen;
        }

        /// Computes the sum of the span-lengths in a `SpanBuffer` object,
        /// both finalized and active.
        ///
        /// This is used by `SplitVec` objects to detect potential
        /// implementation bugs that cause the span-buffer to diverge
        /// from the value-buffer.
        #[inline(always)]
        #[must_use]
        pub fn sum(&self) -> usize {
            self._cache + self.active.unwrap_or(0)
        }

        /// Unconditionally replaces the old value of the cached sum with
        /// the calculated sum of the finalized span-lengths, and returns
        /// a boolean indicating whether the old value was accurate.
        ///
        /// Returns `true` when there was no discrepancy
        ///
        /// This should never return `false` under normal conditions.
        #[allow(dead_code)]
        pub fn check_sum(&mut self) -> bool {
            let recache = self.stable.iter().sum();
            let old = std::mem::replace(&mut self._cache, recache);
            old == recache
        }

        /// Moves all of the spans of `other` into `self`, leaving `other` empty
        ///
        /// This is logically equivalent to a direct [`Vec::append`] call if
        /// `SpanBuffer` held a single vector whose last element was the active
        /// span-length.
        ///
        /// This operation implicitly finalizes the active span-length of `self`
        /// if initialized, before moving all of the finalized spans of `other`
        /// into the buffer of finalized spans in `self`. The active span-length
        /// of `self` is then replaced with that of `other`, leaving `other` with
        /// no finalized spans and an uninitialized active span.
        #[inline]
        pub fn append(&mut self, other: &mut Self) {
            self.flush();
            self.stable.append(&mut other.stable);
            // Because `flush` performs `self.active.take()`, this call to `swap` leaves `other.active() == None`
            std::mem::swap(&mut self.active, &mut other.active);
            (&mut self._cache).add_assign(std::mem::take(&mut other._cache));
        }

        /// Iterate over the span-lengths in an immutably borrowed `SpanBuffer`.
        ///
        /// The iteration covers all of the finalized elements in the span-buffer,
        /// as well as the active span-length, if it is not uninitialized.
        ///
        /// There is no distinction made as to whether the last element produced
        /// by this iterator was finalized or active at the time this method was called.
        #[inline]
        #[must_use]
        pub fn iter(&self) -> Iter<'_> {
            Iter(self.stable.iter().chain(self.active.iter()).copied())
        }

        /// Reverses the operation of finalizing an active span-length
        ///
        /// # Safety
        ///
        /// This method does not check that the stable buffer has any values
        /// to unfreeze, or that the active span-length is uninitialized,
        /// and therefore can clobber existing and cause inconsistencies
        /// in the internal book-keeping if misused.
        ///
        /// It is recommended to use [`unfreeze`], which will check these
        /// conditions and panic if either are violated.
        #[inline]
        #[cfg(feature = "unfreeze_spanbuffer")]
        pub unsafe fn unfreeze_unchecked(&mut self) {
            self.active = Vec::pop(&mut self.stable);
        }

        /// Reverses the operation of finalizing an active span-length
        ///
        /// # Panics
        ///
        /// This method will panic if the active span-length is non-empty,
        /// or if the stable buffer of frozen span-lengths is empty.
        #[inline]
        #[cfg(feature = "unfreeze_spanbuffer")]
        pub fn unfreeze(&mut self) {
            assert!(
                self.active.is_none(),
                "Frozen spans cannot be unfrozen while an active span is initialized"
            );
            let last = Vec::pop(&mut self.stable);
            assert!(last.is_some(), "No frozen spans to unfreeze");
            self.active = last;
        }

        /// Returns `true` if no spans have been initialized or finalized
        ///
        /// # Examples
        /// ```ignore
        /// use ::rust_runtime::internal::splitvec::SpanBuffer;
        ///
        /// let mut p = SpanBuffer::new();
        /// assert!(p.is_empty());
        /// let _ = p.active_mut(); /* This call causes the active span to be initialized */
        /// assert!(!p.is_empty());
        /// ```
        #[must_use]
        #[inline]
        pub fn is_empty(&self) -> bool {
            self.stable.is_empty() && self.active.is_none()
        }

        /// Returns references to the spans of a `SpanBuffer`
        ///
        /// This function breaks the abstraction that `Spanner` consists
        /// solely of a vector with mutable access to only the final index.
        #[must_use]
        #[allow(dead_code)]
        pub fn as_parts(&self) -> (&[usize], Option<usize>) {
            (self.stable.as_slice(), self.active)
        }

        /// Returns the number of spans, frozen or otherwise
        ///
        /// Uninitialized spans are not counted, but even zero-length
        /// active spans count towards the total.
        #[must_use]
        #[allow(dead_code)]
        pub fn count_spans(&self) -> usize {
            self.stable.len() + (self.active.is_some() as usize)
        }

        /// Returns `true` when only one span exists, whether active or finalized
        ///
        /// Should return the same result as `self.count_spans() <= 1` but may
        /// be different in performance.
        ///
        /// # Examples
        ///
        /// ```ignore
        /// let mut sp = Self::new();
        /// assert!(sp.is_contiguous());
        /// *(sp.active_mut()) += 10;
        /// assert!(sp.is_contiguous());
        /// sp.flush();
        /// assert!(sp.is_contiguous());
        /// *(sp.active_mut()) += 10;
        /// assert!(!sp.is_contiguous());
        /// ```
        #[must_use]
        #[inline]
        pub fn is_contiguous(&self) -> bool {
            matches!((self.stable.len(), self.active), (0, _) | (1, None))
        }

        /// Consumes a `SpanBuffer` and converts it into a single `Vec<usize>`,
        /// containing all previously-frozen spans, as well as the active span
        /// as the final element, provided it was initialized.
        ///
        /// If the active span was uninitialized, returns the frozen buffer instead.
        pub fn into_vec(mut self) -> Vec<usize> {
            match self.active {
                None => self.stable,
                Some(last) => {
                    self.stable.push(last);
                    self.stable
                }
            }
        }
    }

    impl std::fmt::Debug for SpanBuffer {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "SpanBuffer({:?} >| {:?})", self.stable, self.active)
        }
    }

    impl std::fmt::Display for SpanBuffer {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{:?}", &self.stable)?;
            if let Some(n) = self.active {
                write!(f, " + ~{}", n)
            } else {
                Ok(())
            }
        }
    }

    /// Iterator associated with [`SpanBuffer`] that yields
    /// span-lengths in FIFO order, with the active span-buffer
    /// as the last yielded value, if it is not uninitialized.
    #[derive(Clone, Debug)]
    pub struct Iter<'a>(
        std::iter::Copied<
            std::iter::Chain<std::slice::Iter<'a, usize>, std::option::Iter<'a, usize>>,
        >,
    );

    impl<'a> Iterator for Iter<'a> {
        type Item = usize;

        #[inline(always)]
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next()
        }
    }

    impl<'a> DoubleEndedIterator for Iter<'a> {
        #[inline(always)]
        fn next_back(&mut self) -> Option<Self::Item> {
            self.0.next_back()
        }
    }

    #[derive(Clone, Debug)]
    pub struct IntoIter<A = std::vec::IntoIter<usize>, B = std::option::IntoIter<usize>>(
        std::iter::Chain<A, B>,
    );

    impl<A, B, I> Iterator for IntoIter<A, B>
    where
        A: Iterator<Item = I>,
        B: Iterator<Item = I>,
    {
        type Item = I;

        #[inline(always)]
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next()
        }
    }

    impl DoubleEndedIterator for IntoIter {
        #[inline(always)]
        fn next_back(&mut self) -> Option<Self::Item> {
            self.0.next_back()
        }
    }

    impl IntoIterator for SpanBuffer {
        type Item = usize;

        type IntoIter = IntoIter;

        /// Consume a `SpanBuffer` and return an interator over the span-lengths it contained.
        ///
        /// The iteration covers all of the finalized elements in the span-buffer,
        /// as well as the active span-length, if it is not uninitialized.
        ///
        /// There is no distinction made as to whether the last element produced
        /// by this iterator was finalized or active at the time this method was called.
        #[must_use]
        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            IntoIter(self.stable.into_iter().chain(self.active.into_iter()))
        }
    }

    impl<'a> IntoIterator for &'a SpanBuffer {
        type Item = &'a usize;

        type IntoIter = IntoIter<std::slice::Iter<'a, usize>, std::option::Iter<'a, usize>>;

        /// Consume a `SpanBuffer` and return an interator over the span-lengths it contained.
        ///
        /// The iteration covers all of the finalized elements in the span-buffer,
        /// as well as the active span-length, if it is not uninitialized.
        ///
        /// There is no distinction made as to whether the last element produced
        /// by this iterator was finalized or active at the time this method was called.
        #[must_use]
        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            IntoIter(self.stable.iter().chain(self.active.iter()))
        }
    }
}

use spanbuffer::SpanBuffer;

/// Virtually segmented [`Vec<T>`]
///
/// `SplitVec<T>` is an enriched variant of `Vec<T>` constrained to `T: Copy`.
///
/// The primary feature presented by `SplitVec<T>` is the facility to virtually
/// partition the underlying buffer into logically grouped contiguous spans,
/// or segments.
///
/// The primary mechanism for this is through two separate buffers, a value-buffer
/// of type `Vec<T>` and a span-buffer of type [`SpanBuffer`], which is effectively
/// a `Vec<usize>`. The span-buffer records the individual length of each contiguous
/// run of values in the value-buffer belonging to the same span or segment. As this
/// is independent of relative length or the start-index, two `SplitVec<T>`
/// values can be appended without any need to re-normalize the spans in the
/// right operand to respect the changed offset from the new 0-index.
#[derive(PartialEq, Eq, Hash, Default, PartialOrd, Ord)]
pub struct SplitVec<T> {
    pub(crate) buffer: Vec<T>,
    pub(crate) spans: SpanBuffer,
}

impl<T> Clone for SplitVec<T>
where
    Vec<T>: Clone,
{
    fn clone(&self) -> Self {
        Self {
            buffer: self.buffer.clone(),
            spans: self.spans.clone(),
        }
    }
}

impl<T> SplitVec<T> {
    /// Create a new `SplitVec<T>` value
    ///
    /// # Examples
    /// ```ignore
    /// let mut s = SplitVec::new();
    /// assert!(s.is_empty());
    /// s.split();
    /// assert!(s.is_empty());
    /// s.force_split();
    /// ```
    ///
    ///
    #[inline(always)]
    #[must_use]
    pub fn new() -> SplitVec<T> {
        SplitVec {
            buffer: Vec::new(),
            spans: SpanBuffer::new(),
        }
    }

    /// Promote a normal `Vec<T>` into a `SplitVec<T>` consisting of only one logical segment,
    /// and using the original owned `Vec<T>` as the backing storage of the result.
    ///
    /// This function does not perform any copies or clones, as it moves the argument into the
    /// result.
    #[inline(always)]
    #[must_use]
    pub fn from_vec(buffer: Vec<T>) -> Self {
        let mut spans = SpanBuffer::new();
        let _ = std::mem::replace(spans.active_mut(), buffer.len());
        Self { spans, buffer }
    }

    /// Finalizes the current span
    ///
    /// Does not cause a new span to be initialized, but any subsequent
    /// calls to methods such as `push_current`, `extend_current`, and
    /// `append_current`, will implicitly cause a new 0-length span
    /// to be initialized just before it is incremented (even if the increment is 0).
    /// a new segment that begins after the currrent final index.
    ///
    /// Only this function (and its derived variant `cleave`) and `concat` will finalize the
    /// current segment (in the case of [`concat`], only the receiver object will have its trailing span
    /// finalized).
    #[inline]
    pub fn split(&mut self) {
        self.spans.flush();
    }

    /// Finalizes the current span even if it is not yet initialized
    ///
    /// Variant of [`split`] that finalizes and terminates segments even if they have not been written
    /// to yet. Most significantly, this will cause a zero-length span to be written if called
    /// after [`split`] with no intervening `xxx_current` calls.
    #[inline]
    pub fn split_force(&mut self) {
        self.spans.flush_force();
    }

    /// In effect, call [`split`] twice in succession. This finalizes both the trailing span,
    /// as well as a zero-length span immediately after it. This is mostly useful for marking
    /// significant indices within the span-buffer.
    ///
    /// Normally, calling [`split`] twice in a row will be equivalent to calling it once.
    #[inline]
    pub fn cleave(&mut self) {
        self.spans.flush();
        self.spans.flush_force();
    }

    /// Returns `true` if the span-buffer sum agrees with the value-buffer length.
    ///
    /// If the return value of this function is `false`, it may indicate an underlying
    /// implementation bug, or incorrect use of the unsafe function `increment_unchecked`.
    #[inline]
    #[must_use]
    pub fn is_balanced(&self) -> bool {
        self.buffer.len() == self.spans.sum()
    }

    /// Increment the length of the current span without any invariant-checking
    ///
    /// This function is unsafe in that its use can cause the invariant
    /// properties of a `SplitVec<T>` to be violated. Its usage is therefore
    /// restricted to internal calls and it is not made public.
    unsafe fn increment(&mut self, amount: usize) {
        self.spans.active_mut().add_assign(amount)
    }

    /// Wrapper around `Vec::push` that appends to the current span.
    ///
    /// If the current span was previously uninitialized, it is pre-populated with `0`
    /// before the span-length increment.
    ///
    /// This function does not perform any segmentation.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let mut sv = SplitVec::from(vec![1, 2, 3]);
    /// sv.push_current(4);
    /// assert_eq!(vec![1,2,3,4], sv.clone_inner());
    /// assert!(sv.is_contiguous());
    /// ```
    #[inline]
    pub fn push_current(&mut self, val: T) {
        self.buffer.push(val);
        unsafe { self.increment(1) };
    }

    /// Wrapper around [`Vec::extend`] that appends to the current span.
    ///
    /// If the current span was previously uninitialized, it is pre-populated with `0`
    /// before the span-length increment.
    ///
    /// This function does not perform any segmentation.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let mut sv = SplitVec::from(vec![1, 2, 3]);
    /// sv.extend_current(&[4,5,6].iter());
    /// assert_eq!(vec![1,2,3,4,5,6], sv.clone_inner());
    /// assert!(sv.is_contiguous());
    /// ```
    pub fn extend_current(&mut self, iter: impl IntoIterator<Item = T>) {
        let l_before = self.buffer.len();
        self.buffer.extend(iter);
        let l_after = self.buffer.len();
        unsafe { self.increment(l_after - l_before) }
    }

    /// Wrapper around [`Vec::extend_from_slice`][vefs] that appends to the current span
    ///
    /// If the current span was previously uninitialized, it is pre-populated with `0`
    /// before the span-length increment.
    ///
    /// This function does not perform any segmentation.
    ///
    /// See [`Vec::extend_from_slice`][vefs] for more information.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let mut sv = SplitVec::from(vec![1, 2, 3]);
    /// sv.extend_current_from_slice(&[4,5,6]);
    /// assert_eq!(vec![1,2,3,4,5,6], sv.clone_inner());
    /// assert!(sv.is_contiguous());
    /// ```
    ///
    /// [vefs]: https://doc.rust-lang.org/stable/std/vec/struct.Vec.html#method.extend_from_slice
    #[inline]
    pub fn extend_current_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        let l = other.len();
        self.buffer.extend_from_slice(other);
        unsafe { self.increment(l) }
    }

    /// Wrapper around [`Vec::append`][vecappend] that appends to the current span
    ///
    /// If the current span was previously uninitialized, it is pre-populated with `0`
    /// before the span-length increment.
    ///
    /// This function does not perform any segmentation.
    ///
    /// Like `Vec::append`, this function leaves `other` empty.
    ///
    /// # Panics
    ///
    /// Panics under the same conditions as `Vec::append` as applied to the
    /// underlying value-buffer.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let mut sv = SplitVec::from(vec![1, 2, 3]);
    /// let mut v = vec![4,5,6];
    /// sv.append_current(&mut v);
    /// assert_eq!(vec![1,2,3,4,5,6], sv.clone_inner());
    /// assert!(v.is_empty());
    /// ```
    ///
    /// [vecappend]: https://doc.rust-lang.org/stable/std/vec/struct.Vec.html#method.append
    #[inline]
    pub fn append_current(&mut self, other: &mut Vec<T>) {
        let l = other.len();
        self.buffer.append(other);
        unsafe { self.increment(l) }
    }

    /// Concatenates two `SplitVec<T>` by appending `other` to `self`
    ///
    /// This operation leaves `other` empty, but preserves the segmentation
    /// of both `self` and `other`
    ///
    /// If there is an unfinalized span in `self` at the time this is called,
    /// it is implicitly finalized, rather than fusing with the first span
    /// in `other`.
    pub fn concat(&mut self, other: &mut Self) {
        debug_assert!(self.is_balanced());
        debug_assert!(other.is_balanced());

        self.buffer.append(&mut other.buffer);
        self.spans.append(&mut other.spans);
    }

    /// Destruct a `SplitVec<T>` into a `Vec<T>`, discarding the span-buffer
    ///
    /// This function moves the value-buffer out of `self` and returns it
    /// without regard to the span-buffer.
    #[inline]
    pub fn into_inner(self) -> Vec<T> {
        self.buffer
    }

    /// Return an iterator over the spans of a `SplitVec<T>`, as slices
    ///
    /// No distinction is made as to whether the final item returned by
    /// the iterator was a finalized or active span at the time this
    /// function was called.
    pub fn spans(&self) -> Spans<'_, '_, T> {
        Spans {
            buf: self.buffer.as_slice(),
            lens: self.spans.iter(),
        }
    }

    /// Returns the number of values in `self`, ignoring segmentation
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let mut sv = SplitVec::new();
    /// assert_eq!(sv.len(), 0);
    /// sv.extend_current_from_slice(&[0u8; 32]);
    /// assert_eq!(sv.len(), 32);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// Returns `true` if there are no elements in the value-buffer,
    /// and no spans have been created (including zero-length spans).
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let mut sv = SplitVec::new();
    /// assert!(sv.is_empty());
    /// sv.split();
    /// /* split does nothing on fresh SplitVecs or another split call */
    /// assert!(sv.is_empty());
    /// sv.extend_current(std::iter::empty());
    /// /* Even though nothing is pushed, the preceding call pre-initializes a zero-length span */
    /// assert!(!sv.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.buffer.is_empty() && self.spans.is_empty()
    }

    /// Return `true` if `self` consists of at most one span, inclusive of
    /// zero-length spans.
    ///
    /// An empty `SplitVec<T>` is considered contiguous, and a
    /// non-contiguous `SplitVec<T>` is never considered empty.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let mut sv = SplitVec::new();
    /// assert!(sv.is_contiguous());
    /// sv.split();
    /// /* split does nothing on fresh SplitVecs or another split call */
    /// assert!(sv.is_contiguous());
    /// sv.extend_current_from_slice(b"Hello World!");
    /// sv.split();
    /// /* Split finalizes the current span but does not re-initialize it */
    /// assert!(sv.is_contiguous());
    /// sv.extend_current(std::iter::empty());
    /// /* Even an empty write initializes a new span if none are active */
    /// assert!(!sv.is_contiguous());
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn is_contiguous(&self) -> bool {
        self.spans.is_contiguous()
    }
}

impl<T> SplitVec<T> {
    pub fn into_parts(self) -> (Vec<T>, Vec<usize>) {
        (self.buffer, self.spans.into_vec())
    }
}

impl<T> From<Vec<T>> for SplitVec<T> {
    fn from(buffer: Vec<T>) -> Self {
        SplitVec::from_vec(buffer)
    }
}

impl<T> From<SplitVec<T>> for Vec<T> {
    fn from(svec: SplitVec<T>) -> Self {
        svec.buffer
    }
}

impl<T> AsRef<Vec<T>> for SplitVec<T> {
    fn as_ref(&self) -> &Vec<T> {
        &self.buffer
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for SplitVec<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buf = &self.buffer[..];
        write!(f, "[|")?;
        for l in self.spans.iter() {
            write!(f, "{:?}|", &buf[..l])?;
            buf = &buf[l..];
        }
        write!(f, "]")
    }
}

impl std::fmt::Display for SplitVec<u8> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let buf: &[u8] = &self.buffer[..];
        write!(f, "[|")?;
        let mut ix: usize = 0;
        for l in self.spans.iter() {
            for &byte in &buf[ix..ix + l] {
                write!(f, "{byte:02x}|")?
            }
            ix += l;
        }
        write!(f, "]")
    }
}

impl<T, I> std::iter::Extend<I> for SplitVec<T>
where
    I: IntoIterator<Item = T>,
{
    fn extend<U: IntoIterator<Item = I>>(&mut self, iter: U) {
        for span in iter {
            self.split();
            self.extend_current(span);
        }
        self.split();
    }
}

impl<T, I> std::iter::FromIterator<I> for SplitVec<T>
where
    I: IntoIterator<Item = T>,
{
    fn from_iter<U: IntoIterator<Item = I>>(iter: U) -> Self {
        let mut ret = SplitVec::new();
        for span in iter {
            ret.extend_current(span);
            ret.split();
        }
        ret
    }
}

/// Iterator over `SplitVec<T>` spans as individual slices
#[derive(Clone, Debug)]
pub struct Spans<'a, 'b, T> {
    buf: &'a [T],
    lens: spanbuffer::Iter<'b>,
}

impl<'a: 'b, 'b, T> Iterator for Spans<'a, 'b, T> {
    type Item = &'a [T];

    /// Advances the iterator and returns the next span
    ///
    /// # Panics
    ///
    /// Panics if the span-buffer and value-buffer had diverged at the time the
    /// original iterator was created.
    ///
    /// In release versions, will only panic if the value-buffer
    /// has fewer elements than expected, and will not panic if it has more
    /// elements than expected.
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.lens.next() {
            None => {
                debug_assert!(
                    self.buf.is_empty(),
                    "Value-buffer has elements not counted in span-buffer"
                );
                None
            }
            Some(len) => {
                let (ret, rest) = self.buf.split_at(len);
                self.buf = rest;
                Some(ret)
            }
        }
    }
}

impl<'a: 'b, 'b, T> DoubleEndedIterator for Spans<'a, 'b, T> {
    /// Removes and returns a span from the end of the iterator.
    ///
    /// # Panics
    ///
    /// Panics if the span-buffer and value-buffer had diverged at the time the
    /// original iterator was created.
    ///
    /// In release versions, will only panic if the value-buffer
    /// has fewer elements than expected, and will not panic if it has more
    /// elements than expected.
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.lens.next_back() {
            None => {
                debug_assert!(self.buf.is_empty(), "Value-buffer has too many elements");
                None
            }
            Some(len) => {
                let mid = self
                    .buf
                    .len()
                    .checked_sub(len)
                    .expect("Value-buffer has too few elements");
                let (rest, ret) = self.buf.split_at(mid);
                self.buf = rest;
                Some(ret)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn iter_spans_test() {
        let mut svec = SplitVec::new();
        (0..10).for_each(|i| {
            svec.extend_current_from_slice(&vec![i; i]);
            svec.split_force();
        });
        let mut spans = svec.spans();
        (0..10).for_each(|i| {
            assert_eq!(Some(vec![i; i].as_slice()), spans.next());
        });
        assert_eq!(None, spans.next());
    }
}
