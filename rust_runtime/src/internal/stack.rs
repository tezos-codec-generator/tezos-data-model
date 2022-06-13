//! Generic trait for standard stack operations
//!
//! This module defines the `Stack` trait, which defines most of
//! the conventional methods of a heterogenous collection with
//! FILO access.
//!
//! This version of `Stack` is specifically optimized for the cases
//! in which it is used internal to the library, and so may not be
//! one-to-one with more general-purpose implementations of stack
//! traits.

/// FILO collection of `Copy` types
///
/// The `Stack` trait defines the basic set of methods for a FILO view of a
/// collection type, which is required to contain, and permit individual
/// insertion, removal, and inspection of items of the trait-level type
/// `Item`, which is required to be `Copy`.
///
/// As it is defined for internal use rather than as a public API, it is
/// partially specialized for the use-cases that exist only within this crate.
///
/// The most notable such specialization is the distinction made between the
/// `push` method, which is marked unsafe, and the `push_validated` method,
/// which is the standard way of safely adding elements to the top of the stack
/// without causing use-specific invariants to be violated. The helper method
/// `push_unchecked` is defined as a shallow wrapper around `push`.
///
/// The trait-bound of `Item: Copy` and the non-reference return value of `peek`
/// and `peek_or` is also a specialization that may not be applicable to
/// external or future use-cases of this trait definition.
pub(crate) trait Stack {
    /// Element type of the `Stack` implementation
    ///
    /// The `Copy` trait-bound permits by-value reference through implicit copies
    /// rather than requiring references.
    type Item: Copy;

    /// Returns the value at the top of the stack, or `None` if empty
    ///
    /// # Notes
    ///
    /// This method signature definition relies on the requirement that `Self::Item`
    /// is `Copy` to return the topmost value by value rather than by reference.
    /// This means that the returned value of `peek` may outlive the top element
    /// of the stack it is a copy of.
    ///
    /// In practice, this means that it is legal
    /// to use the return value of a `peek` operation after any number of `pop`
    /// calls without running afoul of the borrow-checker.
    fn peek(&self) -> Option<Self::Item>;

    /// Returns the topmost value of the Stack, or `default` if empty
    ///
    /// As `Self::Item` is a `Copy`-type, the value of `default` is not
    /// moved if passed in via a local variable.
    fn peek_or(&self, default: Self::Item) -> Self::Item {
        self.peek().unwrap_or(default)
    }

    /// Returns a mutable pointer to topmost item in the stack.
    ///
    /// Unlike `peek`, the value returned, unless `None`, cannot be held
    /// or re-used after the `pop` responsible for removing the corresponding
    /// element.
    fn peek_mut(&mut self) -> Option<&mut Self::Item>;

    /// Removes the topmost value from the stack and returns it, or [`None`][optnone]
    /// if it is empty.
    ///
    /// [optnone]: https://doc.rust-lang.org/stable/std/option/enum.Option.html#variant.None
    fn pop(&mut self) -> Option<Self::Item>;

    /// Removes the topmost value from the stack and returns it, or `default` if it is empty.
    fn pop_or(&mut self, default: Self::Item) -> Self::Item {
        self.pop().unwrap_or(default)
    }

    /// Pushes `item` onto the top of the stack without any invariant-checking,
    /// whether or not this is necessary for the implementing use-case.
    ///
    /// # Safety
    ///
    /// This method will not necessarily be implemented using inherently unsafe
    /// operations, but instead is marked as unsafe to ensure that callers are
    /// aware they may cause invariants to be violated inadvertently.
    unsafe fn push_unchecked(&mut self, item: Self::Item);

    /// Given a closure that returns `None` in the case of a valid value to push,
    /// and `Some(err)` if an error occured, pre-validate and push `item` onto the
    /// Stack.
    ///
    /// If `Err(_)` is returned, the mutably borrowed receiver should be unmodified.
    fn push_validated<Error, F>(&mut self, item: Self::Item, validate: F) -> Result<(), Error>
    where
        F: Fn(Option<Self::Item>, Self::Item) -> Option<Error>,
    {
        match validate(self.peek(), item) {
            None => unsafe {
                self.push_unchecked(item);
                Ok(())
            },
            Some(err) => Err(err),
        }
    }
}

/*
/// Subtrait for stack implementations without invariants
///
/// Extension-trait for `Stack` used only for implementations
/// that do not require any invariant-checking on push.
///
/// Defines one method, `push`, that is merely a 'safe' wrapper around
/// `Stack::push_unchecked`.
pub(crate) trait InvariantFreeStack: Stack {
    #[inline]
    fn push(&mut self, item: <Self as Stack>::Item) {
        unsafe { <Self as Stack>::push_unchecked(self, item) }
    }
}
*/

impl<T: Copy> Stack for Vec<T> {
    type Item = T;

    #[inline]
    fn peek(&self) -> Option<Self::Item> {
        self.last().copied()
    }

    #[inline]
    fn pop(&mut self) -> Option<Self::Item> {
        Vec::pop(self)
    }

    #[inline]
    unsafe fn push_unchecked(&mut self, item: Self::Item) {
        Vec::push(self, item)
    }

    #[inline]
    fn peek_mut(&mut self) -> Option<&mut Self::Item> {
        self.last_mut()
    }
}
