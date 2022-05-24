//! A compartmentalized collection of low-level definitions
/// that allow user-facing types (currently only `ByteParser`) to
/// rely on a stable abstract interface, which can be refined, extended,
/// or refactored more easily than if they were inlined.
use std::{
    fmt::{Debug, Display},
    ops::{Deref, DerefMut},
};

use crate::parse::error::{ParseError, ParseResult, WindowErrorKind};

/// Internal value held by an Indicator, which historically
/// has been an internally-mutable smart-pointer, but is
/// currently implemented one-to-one with its generic type
/// parameter.
type ICell<T> = T;

/// Wrapper around a `usize` that models a monotonically-increasing
/// index into an array-like type.
pub(crate) struct Indicator(ICell<usize>);

impl Indicator {
    fn new() -> Self {
        Self(0usize)
    }

    fn can_advance(&self, n: usize, lim: usize) -> bool {
        self.0 + n <= lim
    }

    fn bounded_advance(&mut self, n: usize, lim: usize) -> (usize, bool) {
        let ret = self.0;
        let can_advance = self.can_advance(n, lim);

        if can_advance {
            self.0 += n;
        }

        (ret, can_advance)
    }

    fn value(&self) -> usize {
        self.0
    }
}

/// A trait with the core methods required for a type to be suitable
/// for acting as a non-backtracking place-marker during sequential
/// access of segments of an array-like structure.
pub trait Marker {
    /// Create a new Market object with initial (absolute) limit `lim`
    fn new(lim: usize) -> Self;

    /// Attempt to 'advance' the place-marker by a given number of indices,
    /// returning a tuple of type `(usize, bool)`, where the first element
    /// is always the index before modification, and the second element
    /// is `true` if and only if the increment was processed successfully.
    ///
    /// As an advance can only fail when the target index (the current index shifted
    /// forward in the buffer by the offset indicated) would be somehow 'illegal'
    /// in the context of the Marker object, passing `0` to a method call of `advance`
    /// should never fail.
    fn advance(&mut self, n: usize) -> (usize, bool);

    /// Returns the current index of the Marker object.
    fn get(&self) -> usize;
}

/// Sub-trait of Marker for objects that include metadata about the
/// numerical maximal increase in offset that is possible to perform
/// in the current state.
pub trait BoundAwareMarker: Marker {
    /// Returns the number of bytes that are in-bounds, i.e. the maximal value that
    /// `self.advance` could be called with that would not fail.
    fn lim(&self) -> usize;

    fn rem(&self) -> usize {
        self.lim() - self.get()
    }
}

/// Offset into a bounded immutable array-like structure, that
/// is aware of the maximal index in the structure it is associated
/// with and will not advance beyond that index.
pub struct Offset {
    _lim: usize,
    cur: Indicator,
}

impl Offset {
    #[allow(dead_code)]
    pub fn promote(self) -> ContextOffset {
        ContextOffset {
            _abs: self._lim,
            cur: self.cur,
            frames: FrameStack::new(),
        }
    }
}

impl Marker for Offset {
    /// Constructor for `Offset` that takes the maximal index in the buffer
    /// it is tracking an offset into, which initializes its internal index
    /// to `0` by default.
    fn new(_lim: usize) -> Self {
        Self {
            _lim,
            cur: Indicator::new(),
        }
    }

    fn advance(&mut self, n: usize) -> (usize, bool) {
        self.cur.bounded_advance(n, self._lim)
    }

    fn get(&self) -> usize {
        self.cur.value()
    }
}

impl BoundAwareMarker for Offset {
    fn lim(&self) -> usize {
        self._lim
    }
}

#[derive(Debug)]
pub enum FrameError {
    NestingViolation { innermost: usize, novel: usize },
}

impl From<FrameError> for WindowErrorKind {
    fn from(f_err: FrameError) -> Self {
        match f_err {
            FrameError::NestingViolation { innermost, novel } => {
                WindowErrorKind::OpenWouldExceedWindow {
                    limit: innermost,
                    request: novel,
                }
            }
        }
    }
}

impl Display for FrameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            &FrameError::NestingViolation { innermost, novel } => f.write_fmt(format_args!(
                "nesting violation: novel window (->{}<-) violates nesting condition of innermost bounds (->{}<-)",
                novel, innermost
            )),
        }
    }
}

pub mod stack;

pub(crate) use self::stack::Stack;
/// Newtype for a heap-allocated stack of context-frames.
struct FrameStack(Vec<usize>);

impl Deref for FrameStack {
    type Target = Vec<usize>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for FrameStack {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Invariant-checker for the implicit condition that all new context-frames must
/// be able to fully nest inside of all previously existing context frames, which
/// by induction only requires that they fit in the most recently created frame.
///
/// Returns `None` if the nesting invariant is met (which happens automatically if there were no
/// extant context-frames to be required to fit within), and otherwise returns `Some(err)` where
/// `err` is the `FrameError` value indicating the reason for the invalidity.
pub fn validate_nesting(innermost: Option<usize>, novel: usize) -> Option<FrameError> {
    if innermost? >= novel {
        None
    } else {
        Some(FrameError::NestingViolation {
            innermost: innermost?,
            novel,
        })
    }
}

impl FrameStack {
    fn new() -> Self {
        Self(Vec::new())
    }

    fn push_frame(&mut self, item: usize) -> Result<(), FrameError> {
        self.push_validated(item, validate_nesting)
    }
}

impl Stack for FrameStack {
    type Item = usize;

    fn peek(&self) -> Option<Self::Item> {
        self.last().copied()
    }

    fn pop(&mut self) -> Option<Self::Item> {
        Vec::pop(self)
    }

    fn push(&mut self, item: Self::Item) {
        Vec::push(self, item)
    }

    fn peek_mut(&mut self) -> Option<&mut Self::Item> {
        self.last_mut()
    }
}

/// `ContextOffset`: Utility type for tracking both the current offset of
/// a static buffer-based parser, as well as its stack of context-windows.
pub struct ContextOffset {
    _abs: usize,
    frames: FrameStack,
    cur: Indicator,
}

impl ContextOffset {
    /// Attempts to create a new context-frame of the specified window-size,
    /// measured from the current value of the offset index. Will fail if the
    /// novel context-frame exceeds the absolute limit set at time of creation,
    /// or if it would violate the nesting invariant of the innermost context-frame
    /// of the stack, assuming it is non-empty.
    pub fn set_fit(&mut self, winsize: usize) -> ParseResult<()> {
        let cur: usize = self.get();
        let new_tgt: usize = cur + winsize;
        if new_tgt > self._abs {
            let bytes_left = self._abs - winsize;
            let request = winsize;
            Err(ParseError::WindowError(
                WindowErrorKind::OpenWouldExceedBuffer {
                    bytes_left,
                    request,
                },
            ))
        } else {
            match self.frames.push_frame(new_tgt) {
                Ok(()) => Ok(()),
                Err(e) => Err(ParseError::from(WindowErrorKind::from(e))),
            }
        }
    }

    /// Tests whether the current offset matches the goal
    /// offset of the innermost context frame. Returns true
    /// when the frame-stack is non-empty and the current
    /// offset matches the innermost frame's target, or false
    /// otherwise.
    ///
    /// Alternatively, returns true if and only if a call
    /// to enforce_target would succeed in the current state.
    pub fn test_target(&self) -> bool {
        if let Some(tgt) = self.frames.peek() {
            self.get() == tgt
        } else {
            false
        }
    }

    /// Pops the innermost context-frame and checks to make sure it existed in the first place,
    /// and that the popped frame's target has been exactly reached.
    pub fn enforce_target(&mut self) -> crate::parse::error::ParseResult<()> {
        let cur: usize = self.get();

        match self.frames.pop() {
            None => Err(ParseError::WindowError(WindowErrorKind::CloseWithoutWindow)),
            Some(tgt) => match tgt.cmp(&cur) {
                std::cmp::Ordering::Less => {
                    Err(ParseError::WindowError(WindowErrorKind::OffsetOverflow {
                        excess: cur - tgt,
                    }))
                }
                std::cmp::Ordering::Equal => Ok(()),
                std::cmp::Ordering::Greater => {
                    Err(ParseError::WindowError(WindowErrorKind::CloseWithResidue {
                        residual: tgt - cur,
                    }))
                }
            },
        }
    }
}

impl Marker for ContextOffset {
    /// Constructor for `Offset` that takes the maximal index in the buffer
    /// it is tracking an offset into, which initializes its internal index
    /// to `0` by default.
    fn new(_abs: usize) -> Self {
        Self {
            _abs,
            frames: FrameStack::new(),
            cur: Indicator::new(),
        }
    }

    fn advance(&mut self, n: usize) -> (usize, bool) {
        self.cur.bounded_advance(n, self.lim())
    }

    fn get(&self) -> usize {
        self.cur.value()
    }
}

impl BoundAwareMarker for ContextOffset {
    fn lim(&self) -> usize {
        self.frames.peek_or(self._abs)
    }
}

pub mod splitvec {
    use std::ops::AddAssign;

    /// `Spanner`: helper type for managing the span-buffer of a `SplitVec`
    ///
    /// A `Spanner` is analogous to a `Vec<usize>` with restricted mutable access:
    /// the only allowed mutations are appending `0` and modifying the final value.
    ///
    /// The actual implementation does not follow this description strictly, but
    /// the details are not significant enough to be worth mentioning.
    ///
    /// It is used to maintain the queue of finalized span-lengths, as well as the
    /// mutable current span-lengths, for a `SplitVec`.
    #[derive(Clone)]
    pub struct Spanner {
        stable: Vec<usize>,
        active: Option<usize>,
        _cache: usize,
    }

    impl std::fmt::Debug for Spanner {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "Spanner({:#?} | {:#?})", self.stable, self.active)
        }
    }

    impl Spanner {
        /// Create a new Spanner object.
        pub fn new() -> Self {
            Self {
                stable: Vec::new(),
                active: None,
                _cache: 0,
            }
        }

        /// Obtain a mutable reference to the length of the currently-active span
        ///
        /// When this is the first call after `Spanner::new` or `Spanner::flush`,
        /// the immediate value pointed to by this reference will be `0`.
        ///
        /// ```
        /// let mut s : Spanner = Spanner::new();
        /// let x : &mut usize = s.active_mut();
        /// assert_eq!(*x, 0usize);
        /// *x = 10;
        /// s.flush();
        /// let y : &mut usize = s.active_mut();
        /// assert_eq!(*y, 0usize);
        /// ```
        pub fn active_mut(&mut self) -> &mut usize {
            self.active.get_or_insert(0)
        }

        /// Freeze the active span-length to its immediate value,
        /// finalizing it and preventing subsequent mutable access.
        ///
        /// After calling this function, calls to `active_mut` will
        /// initialize a new active span-length to `0` and continue to
        /// point to said value until `flush` is called again.
        ///
        /// When called immediately after `Spanner::new` or another
        /// call to `Spanner::flush`, this function has no effect.
        pub fn flush(&mut self) {
            match self.active.take() {
                Some(last) => {
                    self.stable.push(last);
                    self._cache += last;
                }
                None => return,
            };
        }

        /// `force_flush`: variant of the [`flush`] function that
        /// always pushes a finalized value, defaulting to 0 if
        /// the active span-length is uninitialized.
        ///
        /// Unlike [`flush`], this function is not idempotent.
        pub fn force_flush(&mut self) {
            match self.active.take() {
                Some(last) => {
                    self.stable.push(last);
                    self._cache += last;
                }
                None => {
                    self.stable.push(0);
                }
            };
        }

        /// Computes the sum of the span-lengths in a `Spanner` object,
        /// both finalized and active.
        ///
        /// This is used by `SplitVec` objects to detect potential
        /// implementation bugs that cause the span-buffer to diverge
        /// from the value-buffer.
        pub fn sum(&self) -> usize {
            self._cache + self.active.unwrap_or(0)
        }

        /// Combines two `Spanner` objects, implicitly flushing the
        /// current active span-length of the receiver and appending
        /// the span-length buffer of the non-reciever argument to
        /// that of the receiver.
        ///
        /// After calling this function, the active span-length of
        /// the receiver will be replaced with that of the non-receiver
        /// argument.
        pub fn concat(&mut self, mut rhs: Self) {
            self.flush();
            self.stable.append(&mut rhs.stable);
            *(&mut self.active) = rhs.active;
            *(&mut self._cache) += rhs._cache;
            return;
        }

        pub fn iter<'a>(&'a self) -> impl Iterator<Item = usize> + 'a {
            self.stable.iter().chain(self.active.iter()).copied()
        }
    }

    impl IntoIterator for Spanner {
        type Item = usize;

        type IntoIter = std::iter::Chain<std::vec::IntoIter<usize>, std::option::IntoIter<usize>>;

        fn into_iter(self) -> Self::IntoIter {
            self.stable.into_iter().chain(self.active.into_iter())
        }
    }

    /// [`SplitVec`]: Virtually segmented [`Vec`] over [`Copy`] types
    ///
    /// `SplitVec<T>` is an enriched variant of `Vec<T>` constrained to `T: Copy`.
    ///
    /// The primary feature presented by `SplitVec` is the facility to virtually
    /// partition the underlying buffer into logically grouped contiguous spans,
    /// or segments.
    ///
    /// The primary mechanism for this is through two separate buffers, a value-buffer
    /// of type `Vec<T>` and a span-buffer of type [`Spanner`], which is effectively
    /// a `Vec<usize>`. The span-buffer records the individual length of each contiguous
    /// run of values in the value-buffer belonging to the same span or segment. As this
    /// is independent of index, two `SplitVec<T>` values can be appended without
    /// any need to re-normalize the spans in the right operand to respect the changed
    /// offset from the new 0-index.
    #[derive(Clone)]
    pub struct SplitVec<T: Copy> {
        pub(crate) buffer: Vec<T>,
        pub(crate) spans: Spanner,
    }

    impl<T: Copy> From<Vec<T>> for SplitVec<T> {
        fn from(buffer: Vec<T>) -> Self {
            SplitVec::promote_vec(buffer)
        }
    }

    impl<T: Copy> AsRef<Vec<T>> for SplitVec<T> {
        fn as_ref(&self) -> &Vec<T> {
            &self.buffer
        }
    }

    impl<T: Copy> std::ops::Deref for SplitVec<T> {
        type Target = Vec<T>;

        fn deref(&self) -> &Self::Target {
            &self.buffer
        }
    }

    impl<T: std::fmt::Debug + Copy> std::fmt::Debug for SplitVec<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let mut buf = &self.buffer[..];
            write!(f, "[|")?;
            let mut ls = self.spans.iter();
            while let Some(l) = ls.next() {
                write!(f, "{:#?}|", &buf[..l])?;
                buf = &buf[l..];
            }
            write!(f, "]")
        }
    }

    impl std::fmt::Display for SplitVec<u8> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let mut buf: &[u8] = &self.buffer[..];
            write!(f, "[|")?;
            let mut ls = self.spans.iter();
            while let Some(l) = ls.next() {
                write!(f, "{}|", crate::util::hex_of_bytes(&buf[..l]))?;
                buf = &buf[l..];
            }
            write!(f, "]")
        }
    }

    impl<T: Copy> SplitVec<T> {
        /// Promote a normal `Vec<T>` into a `SplitVec<T>` consisting of only one logical segment,
        /// and using the original owned `Vec<T>` as the backing storage of the result.
        ///
        /// This function does not perform any copies or clones, as it moves the argument into the
        /// result.
        pub fn promote_vec(buffer: Vec<T>) -> Self {
            let l = buffer.len();
            let mut spans = Spanner::new();
            *((&mut spans).active_mut()) = l;

            Self { spans, buffer }
        }

        /// Finalize and terminate the trailing segment of a given `SplitVec`, such that any
        /// calls to [`extend_current`], [`push_current`], or [`append_current`] write to
        /// a new segment that begins after the currrent final index.
        ///
        /// Only this function (and its derived variant `cleave`) and `concat` will finalize the
        /// current segment (in the case of [`concat`], only the receiver object will have its trailing span
        /// finalized).
        pub fn split(&mut self) {
            self.spans.flush();
        }

        /// Variant of [`split`] that finalizes and terminates segments even if they have not been written
        /// to yet. Most significantly, this will cause a zero-length span to be written if called
        /// after [`split`] with no intervening `xxx_current` calls.
        fn force_split(&mut self) {
            self.spans.force_flush();
        }

        /// In effect, call [`split`] twice in succession. This finalizes both the trailing span,
        /// as well as a zero-length span immediately after it. This is mostly useful for marking
        /// significant indices within the span-buffer.
        ///
        /// Normally, calling [`split`] twice in a row will be equivalent to calling it once.
        pub fn cleave(&mut self) {
            self.split();
            self.force_split();
        }

        /// Calculate the number of items in the value-buffer that are not accounted for in the span-buffer.
        unsafe fn deficit(&self) -> usize {
            let lbuf = self.buffer.len();
            let lspan = self.spans.sum();
            debug_assert!(lbuf >= lspan);
            lbuf - lspan
        }

        /// Increment the length of the current span independently of writing to the value-buffer
        ///
        /// This function is marked unsafe so that callers are required to guarantee that the
        /// increment magnitude is precisely the number of bytes that would be unaccounted for
        /// following an operation that appends to the value-buffer.
        #[inline]
        unsafe fn increment(&mut self, amount: usize) {
            self.spans.active_mut().add_assign(amount)
        }

        /// Corrects a divergence between the span-buffer and value-buffer by incrementing the current
        /// span-length as necessary.
        ///
        /// Since the condition under which this function call has an effect is implicitly assumed to be
        /// unreachable, this function has no call-sites and is not exported, and so it may be considered dead.
        #[allow(dead_code)]
        unsafe fn balance(&mut self) {
            match self.deficit() {
                0 => return,
                n => self.increment(n),
            }
        }

        pub fn push_current(&mut self, val: T) {
            self.buffer.push(val);
            unsafe { self.increment(1) };
        }

        pub fn extend_current(&mut self, iter: impl IntoIterator<Item = T>) {
            let l_before = self.buffer.len();
            self.buffer.extend(iter);
            let l_after = self.buffer.len();
            unsafe { self.increment(l_after - l_before) }
        }

        pub fn append_current(&mut self, rhs: &mut Vec<T>) {
            let l = rhs.len();
            self.buffer.append(rhs);
            unsafe { self.increment(l) }
        }

        pub fn concat(&mut self, mut rhs: Self) {
            unsafe {
                debug_assert_eq!(self.deficit(), 0);
                debug_assert_eq!(rhs.deficit(), 0);
            }

            self.buffer.append(&mut rhs.buffer);
            self.spans.concat(rhs.spans);
        }

        pub fn forget(self) -> Vec<T> {
            self.buffer
        }

        pub fn new() -> SplitVec<T> {
            SplitVec {
                buffer: Vec::new(),
                spans: Spanner::new(),
            }
        }
    }
}

pub(crate) use splitvec::SplitVec;
