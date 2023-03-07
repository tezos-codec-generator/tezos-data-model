//! Offset and context windows for vector-based `Parser`
//!
//! This module contains assorted traits and types that are
//! primarily intended to handle the stateful components of
//! vector-based `Parser` implementations, contained within
//! the type `ContextOffset`.
//!
//! The traits `Marker` and its subtrait `BoundAwareMarker`
//! are used to encapsulate the desired behavior of

use crate::internal::stack::Stack;
use crate::parse::error::{ParseError, ParseResult, WindowError};
use std::fmt::Debug;

/// Wrapper around [`usize`] that represents monotonically increasing indices
/// into a buffer.
///
/// No promises are made as to how the internal `usize` is stored.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
#[repr(transparent)]
pub struct Index(usize);

impl Index {
    /// Constructs a new `Index` object initialized to `0`
    #[inline(always)]
    #[must_use]
    pub fn new() -> Self {
        Self(0usize)
    }

    /// Advances the held value by `n` unless this would cause it to exceed
    /// `lim`.
    ///
    /// Returns the original value (before incrementation), along with a boolean
    /// value that is equal to  `true` if and only if the increment occurred.
    ///
    /// Ths increment will always occur if `n == 0`, and in general if
    /// `ix + n <= lim`, where `ix` is the value held at the time this method
    /// was called.
    #[inline]
    pub fn increment_checked(&mut self, n: usize, lim: usize) -> (usize, bool) {
        let ret = self.0;
        let is_valid = self.0 + n <= lim;
        if is_valid {
            self.0 += n;
        }
        (ret, is_valid)
    }

    /// Unwraps the `usize` stored within an `Index` value.
    ///
    /// As both `Index` and `usize` are `Copy`, this does not
    /// consume `self`.
    #[must_use]
    #[inline(always)]
    pub fn to_usize(self) -> usize {
        self.0
    }
}

impl AsRef<usize> for Index {
    #[inline(always)]
    #[must_use]
    fn as_ref(&self) -> &usize {
        &self.0
    }
}

impl From<usize> for Index {
    #[inline]
    fn from(ix: usize) -> Self {
        Self(ix)
    }
}

impl From<Index> for usize {
    #[inline]
    fn from(ix: Index) -> Self {
        ix.0
    }
}

macro_rules! index_impl_fmt {
    ( $( $tr:ident ),+ $(,)? ) => {
        $( impl std::fmt::$tr for Index {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                <usize as std::fmt::$tr>::fmt(&self.0, f)
            }
        }
        )+
    };
}

index_impl_fmt![Display];
#[cfg(feature = "index_binary_formatting")]
index_impl_fmt![Binary, Octal, LowerHex, UpperHex];

/// Trackers of a monotonically increasing index for non-backtracking
/// traversal of an array-like type. This includes an invariant absolute limit
/// that the mutable index is not permitted to exceed, but is allowed to reach.
///
/// Implementations of `IndexTracker` are implicitly assumed, and therefore
/// required, to respect an upper limit, which is passed in when an instance
/// is created, and which informs the success and failure of other methods.
pub trait IndexTracker {
    /// Constructor method that takes an argument `abs`, representing
    /// an invariant absolute limit on the index being tracked.
    ///
    /// The initial index-value should always be `0`.
    ///
    /// The case where `abs == 0` is considered valid, but it is allowable
    /// for implementations of this method to assume, for the sake of optimization,
    /// that this is a corner-case, as an `IndexTracker` with an absolute limit of `0` will
    /// always point to `0`.
    #[must_use]
    fn with_limit(abs: usize) -> Self;

    /// Returns the current value of the index being tracked.
    ///
    /// The value returned by this method should never exceed the value returned
    /// by [`limit`]. If this is ever the case, the implementation is unsound.
    #[must_use]
    fn index(&self) -> usize;

    /// Returns the absolute upper bound on the index.
    ///
    /// This value is precisely the argument `abs` that was
    /// passed into the call to [`with_limit`] that created
    /// `self`, or which created the value it was cloned from.
    #[must_use]
    fn absolute_limit(&self) -> usize;

    /// Returns the current upper bound on the index.
    ///
    /// The default implementation of this method is to call
    /// [`absolute_limit`].
    ///
    /// If overridden by implementors, such as in cases where
    /// there is a notion of setting and removing temporary
    /// constraints on the index being tracked,
    /// the value returned by this method must nevertheless
    /// be no greater than the value returned by [`absolute_limit`].
    #[inline]
    #[must_use]
    fn limit(&self) -> usize {
        self.absolute_limit()
    }

    /// Returns the number of indices remaining in the current
    /// range `index..lim`
    /// the current offset.
    fn rem(&self) -> usize {
        debug_assert!(
            self.limit() >= self.index(),
            "Unsound IndexTracker implementation: limit < index"
        );
        self.limit() - self.index()
    }

    /// Attempt to increment the index-value by `n`.
    ///
    /// Returns a tuple containing the original index, as well as a boolean
    /// indicating whether the increment was valid, and therefore, whether
    /// it was performed.
    ///
    /// # Validity
    ///
    /// The only requirements made at the trait-level on what increments
    /// are considered valid or invalid are the following minimal conditions:
    ///  * An increment of `n == 0` is always valid.
    ///  * An increment that would cause the index to exceed the absolute limit is always invalid.
    ///
    /// Beyond those requirements, an increment of `n > 0` may be judged
    /// invalid by implementations that enforce invariants on the index
    /// besides merely `ix <= limit`.
    ///
    /// Saturation is not an option. The index must either remain unchanged
    /// or increase by exactly `n`.
    ///
    /// The following assertions should hold for all `it : &mut impl IndexTracker` and `n : usize`:
    ///
    /// ```ignore
    /// let before : usize = it.index();
    /// let (old, valid) = it.advance(n);
    /// let after : usize = it.index();
    /// assert_eq!(before, old);
    /// if valid {
    ///     assert_eq!(before + n, after);
    /// } else {
    ///     assert_eq!(before, after);
    /// }
    /// ```
    fn advance(&mut self, n: usize) -> (usize, bool);
}

/// Determines whether a new context-window can be created,
///
/// be able to fully nest inside of all previously existing context frames, which
/// by induction only requires that they fit in the most recently created frame.
///
/// Returns `None` if the nesting invariant is met (which happens automatically if there were no
/// extant context-frames to be required to fit within), and otherwise returns `Some(err)` where
/// `err` is the `FrameError` value indicating the reason for the invalidity.
#[inline]
const fn detect_error(innermost: Option<usize>, request: usize) -> Option<WindowError> {
    match innermost {
        Some(limit) if request > limit => {
            Some(WindowError::OpenWouldExceedWindow { limit, request })
        }
        _ => None,
    }
}

/// Vector-based stack of target offsets representing the implicit bounds of
/// context windows.
///
/// The elements of a `FrameStack` are guaranteed by induction to be sorted
/// with the smallest value at the top of the stack.
#[derive(Debug)]
#[repr(transparent)]
pub struct FrameStack(Vec<usize>);

impl FrameStack {
    /// Creates a new framestack
    fn new() -> Self {
        Self(Vec::new())
    }

    /// Pushes a new target offset, returning a `ParseResult<()>`
    /// indicating whether the push was performed or whether it
    /// was not legal.
    ///
    /// Even though the return type of this function does not specify as such,
    /// if `Err(e)` is returned, with `e : ParseError` is guaranteed to
    /// match `WindowError(OpenWouldExceedWindow { .. })`
    fn push_frame(&mut self, target: usize) -> ParseResult<()> {
        Ok(self.push_validated(target, detect_error)?)
    }
}

impl Stack for FrameStack {
    /// Type of value pushed onto and popped off of a `FrameStack`, representing
    /// a target index for the offset to reach exactly before the context window
    /// can be closed.
    type Item = usize;

    /// Returns a copy of the item at the top of the `FrameStack` without modifying
    /// the stack itself.
    ///
    /// Returns `None` if and only if the stack is empty, i.e. there are no extant
    /// context windows.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// # use ::tedium::internal::{stack::Stack, offset::FrameStack};
    /// let mut fs : FrameStack = FrameStack::new();
    /// assert_eq!(fs.peek(), None);
    /// ```
    fn peek(&self) -> Option<Self::Item> {
        self.0.last().copied()
    }

    fn peek_mut(&mut self) -> Option<&mut Self::Item> {
        Vec::peek_mut(&mut self.0)
    }

    fn pop(&mut self) -> Option<Self::Item> {
        Vec::pop(&mut self.0)
    }

    unsafe fn push_unchecked(&mut self, item: Self::Item) {
        Vec::push(&mut self.0, item)
    }
}

/// `ContextOffset`: Utility type for tracking both the current offset of
/// a static buffer-based parser, as well as its stack of context-windows.
#[derive(Debug)]
pub struct ContextOffset {
    abs: usize,
    frames: FrameStack,
    cur: Index,
}

impl ContextOffset {
    /// Attempts to create a new context-frame of the specified window-size,
    /// measured from the current value of the offset index. Will fail if the
    /// novel context-frame exceeds the absolute limit set at time of creation,
    /// or if it would violate the nesting invariant of the innermost context-frame
    /// of the stack, assuming it is non-empty.
    pub fn set_fit(&mut self, winsize: usize) -> ParseResult<()> {
        let cur: usize = self.index();
        let new_tgt: usize = cur + winsize;
        if new_tgt > self.abs {
            let bytes_left = self.abs - winsize;
            let request = winsize;
            Err(ParseError::Window(WindowError::OpenWouldExceedBuffer {
                bytes_left,
                request,
            }))
        } else {
            self.frames.push_frame(new_tgt)
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
    pub fn test_target(&self) -> ParseResult<bool> {
        let cur = self.index();

        if let Some(tgt) = self.frames.peek() {
            match tgt.cmp(&cur) {
                std::cmp::Ordering::Equal => Ok(true),
                std::cmp::Ordering::Greater => Ok(false),
                std::cmp::Ordering::Less => Err(ParseError::Window(WindowError::OffsetOverflow {
                    excess: cur - tgt,
                })),
            }
        } else {
            Ok(false)
        }
    }

    /// Attempt to closes the innermost context-frame.
    ///
    /// This method returns `Ok(())` when the current offset
    /// exactly equals the innermost target offset, and fails
    /// otherwise, including the case where there are no
    /// context-windows to close.
    ///
    /// # Errors
    ///
    /// If there are no open context windows, returns a suitably wrapped
    /// [`CloseWithoutWindow`][cwow] error.
    ///
    /// If there are leftover bytes in the innermost context window between The
    /// actual and target offsets, returns a suitably wrapped [`CloseWithResidue`][cwr]
    /// error.
    ///
    /// In the rare case that the actual offset has somehow surpassed the target offset,
    /// returns a suitably wrpaped [`OffsetOverflow`][oof] error.
    ///
    /// [cwow]: crate::parse::error::WindowError::CloseWithoutWindow
    /// [cwr]: crate::parse::error::WindowError::CloseWithResidue
    /// [oof]: crate::parse::error::WindowError::OffsetOverflow
    pub fn enforce_target(&mut self) -> crate::parse::error::ParseResult<()> {
        let cur: usize = self.index();

        match self.frames.pop() {
            None => Err(ParseError::Window(WindowError::CloseWithoutWindow)),
            Some(tgt) => match tgt.cmp(&cur) {
                std::cmp::Ordering::Equal => Ok(()),
                std::cmp::Ordering::Greater => {
                    Err(ParseError::Window(WindowError::CloseWithResidue {
                        residual: tgt - cur,
                    }))
                }
                std::cmp::Ordering::Less => Err(ParseError::Window(WindowError::OffsetOverflow {
                    excess: cur - tgt,
                })),
            },
        }
    }
}

impl IndexTracker for ContextOffset {
    /// Constructor for `ContextOffset` that takes the maximal index in the buffer
    /// it is tracking an offset into, and initializes its internal index
    /// to `0` by default.
    fn with_limit(abs: usize) -> Self {
        Self {
            abs,
            frames: FrameStack::new(),
            cur: Index::new(),
        }
    }

    #[inline]
    #[must_use]
    fn index(&self) -> usize {
        self.cur.to_usize()
    }

    /// Returns the immutable absolute limit of `self`
    #[inline(always)]
    #[must_use]
    fn absolute_limit(&self) -> usize {
        self.abs
    }

    /// Returns the upper bound of the narrowest context-window,
    /// or the absolute limit if there are no context windows set.
    #[inline]
    #[must_use]
    fn limit(&self) -> usize {
        self.frames.peek_or(self.abs)
    }

    #[inline]
    fn advance(&mut self, n: usize) -> (usize, bool) {
        self.cur.increment_checked(n, self.limit())
    }
}
