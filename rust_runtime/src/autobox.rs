use crate::conv::target::Target;
use crate::conv::{len::Estimable, Decode, Encode};
use crate::parse::{ParseResult, Parser};
use std::fmt::Debug;
use std::ops::Deref;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AutoBox<T: Encode + Decode + Estimable + Debug> {
    _box: Box<T>,
}

impl<T> Debug for AutoBox<T>
where
    T: Encode + Decode + Estimable + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[AutoBox|{:?}]", self._box.as_ref())
    }
}

impl<T: Encode + Decode + Estimable + Debug> AutoBox<T> {
    pub fn new(val: T) -> Self {
        Self {
            _box: Box::new(val),
        }
    }
}

impl<T> From<T> for AutoBox<T>
where
    T: Encode + Decode + Estimable + Debug,
{
    fn from(val: T) -> Self {
        Self::new(val)
    }
}

impl<T> From<Box<T>> for AutoBox<T>
where
    T: Encode + Decode + Estimable + Debug,
{
    fn from(_box: Box<T>) -> Self {
        Self { _box }
    }
}

impl<T> Deref for AutoBox<T>
where
    T: Encode + Decode + Estimable + Debug,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self._box.deref()
    }
}

impl<T: Encode + Decode + Estimable + Debug> Encode for AutoBox<T> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        crate::write_all_to!(self._box.as_ref() => buf)
    }
}

impl<T: Encode + Decode + Estimable + Debug> Decode for AutoBox<T> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        Ok(AutoBox {
            _box: Box::new(T::parse(p)?),
        })
    }
}

impl<T: Encode + Decode + Estimable + Debug> Estimable for AutoBox<T> {
    const KNOWN: Option<usize> = T::KNOWN;

    fn unknown(&self) -> usize {
        self._box.as_ref().unknown()
    }
}
