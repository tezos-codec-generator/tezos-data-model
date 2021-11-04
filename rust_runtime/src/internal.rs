#[allow(unused_imports)]
use std::cell::{Cell, RefCell};

type ICell<T> = Cell<T>;

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

pub trait Marker {
    fn advance(&self, n: usize) -> (usize, bool);
    fn get(&self) -> usize;
}

pub struct Offset {
    _lim: usize,
    cur: Indicator,
}

impl Offset {
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