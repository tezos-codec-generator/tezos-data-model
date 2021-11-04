//! A compartmentalized collection of low-level definitions
/// that allow user-facing types (currently only `ByteParser`) to
/// rely on a stable abstract interface, which can be refined, extended,
/// or refactored more easily than if they were inlined.

#[allow(unused_imports)]
use std::cell::{Cell, RefCell};

type ICell<T> = Cell<T>;

/// Internally mutable smart-pointer to a `usize` that models a monotonically-increasing
/// index into an array-like type.
pub(crate) struct Indicator(ICell<usize>);

impl Indicator {
    fn new() -> Self {
        Self(Cell::new(0usize))
    }

    fn bounded_advance(&self, n: usize, lim: usize) -> (usize, bool) {
        let m : usize = self.0.get();
        let can_advance = m + n <= lim;
        if can_advance {
            self.0.set(m+n)
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
    /// Attempt to 'advance' the place-marker by a given number of indices,
    /// returning a tuple of type `(usize, bool)`, where the first element
    /// is always the index before modification, and the second element
    /// is `true` if and only if the increment was processed successfully.
    /// 
    /// Note that as the self value is borrowed immutably, each implementor
    /// of Marker is intended to track its index via an internally mutable
    /// structure, such as `Cell<T>`.
    /// 
    /// As an advance can only fail when the target index (the current index plus
    /// the offset indicated) would be somehow 'illegal' in the context of the
    /// Marker object, passing `0` to a method call of `advance` should never fail.
    /// 
    /// # Examples
    /// ```
    /// let i = x.get();
    /// let (j, adv) = x.advance(0);
    /// assert_eq!(i, j);
    /// assert!(adv);
    /// let (k, adv) = x.advance(5);
    /// assert_eq!(k, i + (if adv then { 5 } else { 0 }));
    /// ```
    fn advance(&self, n: usize) -> (usize, bool);

    /// Returns the current index of the Marker object.
    fn get(&self) -> usize;
}

/// Offset into a bounded immutable array-like structure, that
/// is aware of the maximal index in the structure it is associated
/// with and will not advance beyond that index.
pub struct Offset {
    _lim: usize,
    cur: Indicator,
}

impl Offset {
    /// Constructor for `Offset` that takes the maximal index in the buffer
    /// it is tracking an offset into, which initializes its internal index
    /// to `0` by default.
    pub fn new(_lim: usize) -> Self {
        Self { _lim, cur: Indicator::new() }
    }
}

impl Marker for Offset {
    fn advance(&self, n: usize) -> (usize, bool) {
        self.cur.bounded_advance(n, self._lim)
    }

    fn get(&self) -> usize {
        self.cur.value()
    }
}