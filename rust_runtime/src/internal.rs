//! A compartmentalized collection of low-level definitions
/// that allow user-facing types (currently only `ByteParser`) to
/// rely on a stable abstract interface, which can be refined, extended,
/// or refactored more easily than if they were inlined.
use std::{
    fmt::{Debug, Display},
    ops::{Deref, DerefMut},
};

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
    /// in the context of the Marker object, passing `0` to a method call of`advance`
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

pub(crate) trait Stack {
    /// Type of the values that are pushed onto the stack.
    type Item: Copy;

    /// Return the topmost value of the Stack, or `None` if it is empty
    fn peek(&self) -> Option<Self::Item>;

    /// Return the topmost value of the Stack, or `default` if it is empty
    fn peek_or(&self, default: Self::Item) -> Self::Item {
        self.peek().unwrap_or(default)
    }

    /// Return a mutable reference to the topmost value of the stack without otherwise
    /// mutating the stack itself.
    fn peek_mut(&mut self) -> Option<&mut Self::Item>;

    /// Like `peek`, but the topmost value of the stack is removed if it exists.
    fn pop(&mut self) -> Option<Self::Item>;

    /// Like `peek_or`, but the value returned is removed from the stack if it was not empty.
    fn pop_or(&mut self, default: Self::Item) -> Self::Item {
        self.pop().unwrap_or(default)
    }

    /// Push `item` onto the top of the stack.
    fn push(&mut self, item: Self::Item);

    /// Given a closure that returns `None` in the case of a valid value to push,
    /// and `Some(err)` if an error occured, pre-validate and push `item` onto the
    /// Stack.
    ///
    /// If `Err(_)` is returned, the mutably borrowed receiver should be unmodified.
    fn push_validated<Error, F: Fn(Option<Self::Item>, Self::Item) -> Option<Error>>(
        &mut self,
        item: Self::Item,
        validate: F,
    ) -> Result<(), Error> {
        match validate(self.peek(), item) {
            None => Ok(self.push(item)),
            Some(err) => Err(err),
        }
    }
}

impl<T: Copy> Stack for Vec<T> {
    type Item = T;

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
    pub fn set_fit(&mut self, winsize: usize) {
        let cur: usize = self.get();
        let new_tgt: usize = cur + winsize;
        if new_tgt > self._abs {
            panic!(
                "Target offset of {}+->{} would overflow buffer (len: {})",
                cur, winsize, self._abs
            );
        }

        self.frames.push_frame(new_tgt).unwrap()
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

    /// Pops the innermost context-frame and panics if it was not exactly reached by the
    /// offset indicator at the time of invocation (including if there was no frame to pop in the first place).
    pub fn enforce_target(&mut self) {
        let cur: usize = self.get();

        match self.frames.pop() {
            None => panic!("ContextOffset::enforce_target: No target to enforce!"),
            Some(tgt) => assert_eq!(cur, tgt, "ContextOffset::enforce_target: current offset ({}) did not match innermost frame bounds (->{})", cur, tgt),
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
