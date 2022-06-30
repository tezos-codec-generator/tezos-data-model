use crate::error::LengthError;

/// Marker trait for types suitable as implementations for `LimSeq` and `FixSeq`
pub trait IsBoundedSeq {
    type Elem;
    const LIMIT: usize;
}

/// Extension trait for implementations of `LimSeq` and `FixSeq`
pub trait BoundedSeqImpl
where
    Self: IsBoundedSeq + std::ops::Deref<Target = [<Self as IsBoundedSeq>::Elem]>,
{
    /// Pushes an element to the end of the bounded sequence, without checking
    /// whether this would violate the length-limit, or even whether this
    /// limit has already been exceeded.
    ///
    /// # Safety
    ///
    /// This method has no default implementation, and therefore is not
    /// *inherently* unsafe at the trait-level. However, it is fully expected that
    /// certain implementations will make use of inherently unsafe operations,
    /// including ones that may cause Undefined Behavior if the type-level capacity
    /// is violated.
    ///
    /// Even in cases where there is no risk of Undefined Behavior, this method
    /// may append beyond the expected capacity of a bounded-length collection
    /// type; doing so may thwart optimizations, and even produce
    /// runtime panics when infallible operations, such as [`Encode`] operations, are
    /// called on such oversaturated collections.
    ///
    /// [`Encode`]: crate::conv::Encode
    unsafe fn push_unchecked(&mut self, value: Self::Elem);

    /// Attempt to add an element to the end of the bounded sequence.
    ///
    /// Returns `Ok(())` if the element was added successfully, that is,
    /// without exceeding the size-limit of `self`.
    ///
    /// # Errors
    ///
    /// Returns [`LengthError::TooLong`](crate::error::LengthError::TooLong)
    /// if `self.len() >= Self::LIMIT`.
    ///
    ///
    ///
    /// returning `OK(())` if the inherent length-limit was not violated,
    /// and `Err(L)
    fn try_push(&mut self, value: Self::Elem) -> Result<(), LengthError> {
        if self.len() < Self::LIMIT {
            unsafe {
                self.push_unchecked(value);
            }
            Ok(())
        } else {
            Err(LengthError::TooLong {
                limit: Self::LIMIT,
                actual: Self::LIMIT + 1,
            })
        }
    }
}
