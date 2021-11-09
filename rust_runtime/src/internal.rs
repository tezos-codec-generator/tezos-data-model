//! A compartmentalized collection of low-level definitions
/// that allow user-facing types (currently only `ByteParser`) to
/// rely on a stable abstract interface, which can be refined, extended,
/// or refactored more easily than if they were inlined.

#[allow(unused_imports)]
use std::cell::{Cell, RefCell};

use std::{collections::VecDeque, fmt::{Debug, Display}};

type ICell<T> = Cell<T>;

/// Internally mutable smart-pointer to a `usize` that models a monotonically-increasing
/// index into an array-like type.
pub(crate) struct Indicator(ICell<usize>);

impl Indicator {
    fn new() -> Self {
        Self(Cell::new(0usize))
    }

    fn bounded_advance(&self, n: usize, lim: usize) -> (usize, bool) {
        let m: usize = self.0.get();
        let can_advance = m + n <= lim;
        if can_advance {
            self.0.set(m + n)
        } else {
            self.0.set(m)
        }
        (m, can_advance)
    }

    fn value(&self) -> usize {
        self.0.get()
    }
}

/// A trait with the core methods required for a type to be suitable
/// for acting as a non-backtracking place-marker during sequential
/// access of segments of an array-like structure.
pub trait Marker {
    fn new(lim: usize) -> Self;

    /// Attempt to 'advance' the place-marker by a given number of indices,
    /// returning a tuple of type `(usize, bool)`, where the first element
    /// is always the index before modification, and the second element
    /// is `true` if and only if the increment was processed successfully.
    ///
    /// As an advance can only fail when the target index (the current index plus
    /// the offset indicated) would be somehow 'illegal' in the context of the
    /// Marker object, passing `0` to a method call of `advance` should never fail.
    fn advance(&mut self, n: usize) -> (usize, bool);

    /// Returns the current index of the Marker object.
    fn get(&self) -> usize;
}

pub trait BoundAwareMarker: Marker {
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
        ContextOffset { _abs: self._lim, cur: self.cur, frames: FrameStack::new() }
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
    NestingViolation { limit: usize, value: usize },
}

impl Display for FrameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            &FrameError::NestingViolation { limit, value } => f.write_fmt(format_args!(
                "nesting violation: new window (->{}) would exceed innermost bounds (->{})",
                value, limit
            )),
        }
    }
}

pub struct FrameStack(VecDeque<usize>);

impl FrameStack {
    pub fn new() -> Self {
        Self(VecDeque::new())
    }

    pub fn peek(&self) -> Option<usize> {
        self.0.back().map(|&u| u)
    }

    pub fn peek_or(&self, def: usize) -> usize {
        self.peek().unwrap_or(def)
    }

    pub fn push(&mut self, n: usize) -> Result<(), FrameError> {
        match self.peek() {
            Some(m) if m < n => Err(FrameError::NestingViolation { limit: m, value: n }),
            _ => Ok(self.0.push_back(n)),
        }
    }

    pub fn pop(&mut self) -> Option<usize> {
        self.0.pop_back()
    }

    #[allow(dead_code)]
    pub fn pop_or(&mut self, def: usize) -> usize {
        self.pop().unwrap_or(def)
    }
}

pub struct ContextOffset {
    _abs: usize,
    frames: FrameStack,
    cur: Indicator,
}

impl ContextOffset {

    pub fn set_fit(&mut self, winsize: usize) {
        let cur: usize = self.get();
        let new_tgt: usize = cur + winsize;
        if new_tgt > self._abs {
            panic!(
                "Target offset of {}+->{} would overflow buffer (len: {})",
                cur, winsize, self._abs
            );
        }

        self.frames.push(new_tgt).unwrap()
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