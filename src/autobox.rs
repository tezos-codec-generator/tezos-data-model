//! Newtype around [`Box<T>`][box] for defining auto-recursive codecs
//!
//! [`AutoBox<T>`] is an alternative to `Box<T>` that is intended only
//! for definining auto-recursive codecs. It is also suitable for defining
//! codecs with mutual recursion, to a lesser extent.
//!
//! While nominally equivalent to standard `Box<T>`, which `AutoBox<T>` is a
//! newtype pattern around, the fact that `Box<T>` is a fundamental type
//! means that downstream code can freely write `impl Encode for Box<MyType>`
//! without violating the orphan rule, which is not a sound practice;
//! only types that are already `MyType: Encode` should be encodable even in
//! as `Box<MyType>`, and the implementation details for `Encode` on the two
//! types should not be allowed to diverge even accidentally; furthermore,
//! it would still be ambiguous whether `Box::new(x).to_bytes()` was intended
//! to be `<Box<T> as Encode>::to_bytes(&Box::new(x))` or
//! `<T as Encode>::to_bytes(&*Box::new(x))`, even if the implementations
//! did not diverge.
//!
//!
//! # Examples
//!
//! ```
//! # use ::rust_runtime::{AutoBox, Encode, Decode, Estimable, Target, resolve_zero};
//! pub struct U8Seq(u8, Option<AutoBox<U8Seq>>);
//!
//! impl Encode for U8Seq {
//!     fn write_to<U: Target>(&self, buf: &mut U) -> usize {
//!         <u8 as Encode>::write_to(&self.0, buf) +
//!         <Option<AutoBox<U8Seq>> as Encode>::write_to(&self.1, buf) +
//!         resolve_zero!(buf)
//!     }
//! }
//!
//! let val: U8Seq = U8Seq(5, Some(AutoBox::new(U8Seq(7, None))));
//! assert_eq!(val.to_bytes(), vec![0x05, 0xff, 0x07, 0x00]);
//! ```
//!
//!
//! This library does not provide any implementations of `Encode`, `Decode`,
//! or `Estimable` for `Box<T>` due to deref-ambiguity in the intended
//! dispatch type of `Box::new(5u8).write_to(buf)`, between
//! `<Box<T> as Encode>::write_to` and `<T as Encode>::write_to`.
//! Furthermore, as `Box<T>` is marked as `fundamental`, it is legal
//! for downstream crates to write `impl Encode for Box<MyType>`
//! even if `MyType` is not itself `Encode`, which introduces further
//! ambiguity.
//!
//! While the nature of encoding would
//! mean that there ought to be no difference between the two methods in
//! terms of operational semantics (i.e. boxing should not change the encoding)
//! such an implementation may be confusing nevertheless.
//!
//! [box]: https://doc.rust-lang.org/std/boxed/struct.Box.html

use crate::conv::target::Target;
use crate::conv::{len::Estimable, Decode, Encode};
use crate::parse::{ParseResult, Parser};
use std::fmt::{Debug, Display};

/// An abstract type for encapsulating type-recursion safely
///
/// `AutoBox<T>` is analogous, and indeed an opaque newtype,
/// around `Box<T>`. It is intended as a means to avoid adding
/// ambiguous methods to the smart-pointer (`Deref`) type `Box<T>`,
/// while still faciliting the definition of self-recursive types.
///
/// The 'Auto' in autobox refers to the self-referential nature
/// of its primary use-case, and is not intended to suggest
/// any notion of 'automation' or 'automaticity'.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct AutoBox<T> {
    _box: Box<T>,
}

impl<T> AutoBox<T> {
    /// Allocates memory on the heap and then places `x` into it
    ///
    /// Because this ultimately calls [Box::new](https://doc.rust-lang.org/std/boxed/struct.Box.html#method.new),
    /// it shares the same property that heap allocations will not occur if `T` is zero-sized.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rust_runtime::AutoBox;
    /// let five = AutoBox::new(5u8);
    /// ```
    ///
    #[must_use]
    pub fn new(x: T) -> Self {
        Self { _box: Box::new(x) }
    }

    /// Converts an existing `Box<T>` into an `AutoBox<T>` with a direct move
    #[must_use]
    #[inline]
    pub fn from_boxed(_box: Box<T>) -> Self {
        Self { _box }
    }

    /// Consumes an `AutoBox<T>` and returns the `Box<T>` it contains
    ///
    /// # Examples
    ///
    /// ```
    /// # use rust_runtime::AutoBox;
    /// let five = AutoBox::new(5u8);
    /// assert_eq!(&5u8, Box::as_ref(&five.into_box()));
    /// ```
    #[must_use]
    #[inline]
    pub fn into_box(self) -> Box<T> {
        self._box
    }

    /// Consumes the `AutoBox<T>` and returns the owned value of type `T`
    /// contained within.
    /// ```
    /// # use rust_runtime::AutoBox;
    /// let five = AutoBox::new(5u8);
    /// assert_eq!(5u8, five.into_inner());
    /// ```
    #[must_use]
    #[inline]
    pub fn into_inner(self) -> T {
        *(self._box)
    }

    /// Returns a mutable reference to the underlying `Box<T>` inside of a mutably borrowed `AutoBox<T>`
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use rust_runtime::AutoBox;
    /// let mut five = AutoBox::new(5u8);
    /// assert_eq!(&5u8, five.as_inner());
    /// *(five.as_mut_boxed()) = Box::new(3u8);
    /// assert_eq!(&3u8, five.as_inner());
    /// ```
    #[must_use]
    #[inline]
    pub fn as_mut_boxed(&mut self) -> &mut Box<T> {
        &mut self._box
    }

    /// Returns a mutable pointer to the value stored inside a mutably borrowed `AutoBox<T>`
    ///
    /// # Examples
    ///
    /// ```
    /// # use rust_runtime::AutoBox;
    /// let mut x = AutoBox::new(5u8);
    /// assert_eq!(x.as_inner(), &5u8);
    /// *(x.as_mut_inner()) += 3;
    /// assert_eq!(x.as_inner(), &8u8);
    /// ```
    #[must_use]
    #[inline]
    pub fn as_mut_inner(&mut self) -> &mut T {
        <Box<T> as AsMut<T>>::as_mut(&mut self._box)
    }

    /// Returns a reference to the value contained within an `AutoBox`
    ///
    /// # Examples
    ///
    /// ```
    /// # use rust_runtime::autobox::AutoBox;
    /// let five = AutoBox::new(5u8);
    /// assert_eq!(&5u8, five.as_inner());
    /// ```
    #[must_use]
    #[inline]
    pub fn as_inner(&self) -> &T {
        <Box<T> as AsRef<T>>::as_ref(&self._box)
    }
}

impl<T> Clone for AutoBox<T>
where
    Box<T>: Clone,
{
    #[must_use]
    fn clone(&self) -> Self {
        Self {
            _box: self._box.clone(),
        }
    }
}

impl<T> std::default::Default for AutoBox<T>
where
    Box<T>: std::default::Default,
{
    #[must_use]
    fn default() -> Self {
        Self {
            _box: Default::default(),
        }
    }
}

impl<T: Debug> Debug for AutoBox<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as Debug>::fmt(self.as_inner(), f)
    }
}

impl<T: Display> Display for AutoBox<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as Display>::fmt(self.as_inner(), f)
    }
}

impl<T> AsRef<T> for AutoBox<T> {
    fn as_ref(&self) -> &T {
        self._box.as_ref()
    }
}

impl<T> AsMut<T> for AutoBox<T> {
    fn as_mut(&mut self) -> &mut T {
        self.as_mut_inner()
    }
}

impl<T> AsRef<Box<T>> for AutoBox<T> {
    fn as_ref(&self) -> &Box<T> {
        &self._box
    }
}

impl<T> From<T> for AutoBox<T> {
    fn from(x: T) -> Self {
        Self { _box: Box::new(x) }
    }
}

impl<T> From<Box<T>> for AutoBox<T> {
    fn from(_box: Box<T>) -> Self {
        Self { _box }
    }
}

impl<T: Encode> Encode for AutoBox<T> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        <T as Encode>::write_to(self._box.as_ref(), buf)
    }
}

impl<T: Decode> Decode for AutoBox<T> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        match T::parse(p) {
            Ok(t) => Ok(AutoBox::new(t)),
            Err(e) => Err(e),
        }
    }
}

impl<T: Estimable> Estimable for AutoBox<T> {
    const KNOWN: Option<usize> = T::KNOWN;

    fn unknown(&self) -> usize {
        <T as Estimable>::unknown(self._box.as_ref())
    }
}
