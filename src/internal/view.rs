use crate::internal::stack::Stack;
use crate::parse::buffer::SliceBuffer;

#[cfg(feature = "smallvec_viewstack")]
extern crate smallvec;

#[cfg(feature = "smallvec_viewstack")]
pub mod smallvec_viewstack {
    //! Implementation of `ViewStack<'a>` based on `SmallVec`, which requires no
    //! heap allocations provided it remains small enough.

    use crate::parse::buffer::SliceBuffer;
    use ::smallvec::SmallVec;

    /// Number of elements that can be held simultaneously by a `SmallVec`-based
    /// `ViewStack<'a>` before it requires heap allocation.
    ///
    /// As an un-windowed `ViewStack` has one element, this number is one higher
    /// than the maximum number of open context-windows at a given time that
    /// avoid heap allocation.
    pub const INLINE_ALLOC: usize = 8;

    /// Window-model type consising of contiguous disjoint `SliceBuffer<'a>` values
    ///
    /// Implemented using `SmallVec`, with an array-size of [`INLINE_ALLOC`]
    #[derive(Clone, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
    pub struct ViewStack<'a>(pub(super) SmallVec<[SliceBuffer<'a>; INLINE_ALLOC]>);

    impl<'a> ViewStack<'a> {
        /// Constructs a new, empty `ViewStack`
        #[allow(dead_code)]
        pub fn new() -> Self {
            Self(SmallVec::new())
        }

        /// Constructs a new `ViewStack` containing a single passed-in element
        pub fn from_buffer(sbuf: SliceBuffer<'a>) -> Self {
            Self(SmallVec::from_buf([sbuf]))
        }
    }
}

#[cfg_attr(feature = "smallvec_viewstack", allow(dead_code))]
pub mod vec_viewstack {
    use crate::parse::buffer::SliceBuffer;
    /// Window-model type consising of contiguous disjoint `SliceBuffer<'a>` values
    ///
    /// Implemented using a regular `Vec` over `SliceBuffer<'a>`
    ///
    /// Setting the `smallvec_viewstack` feature flag will cause this implementation
    /// to be shadowed by an alternative that is based on `SmallVec`
    #[derive(Clone, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
    pub struct ViewStack<'a>(pub(super) Vec<SliceBuffer<'a>>);

    impl<'a> ViewStack<'a> {
        /// Constructs a new, empty `ViewStack`
        #[allow(dead_code)]
        pub fn new() -> Self {
            Self(Vec::new())
        }

        /// Constructs a new `ViewStack` containing a single passed-in element
        pub fn from_buffer(sbuf: SliceBuffer<'a>) -> Self {
            Self(vec![sbuf])
        }
    }
}

#[cfg(feature = "smallvec_viewstack")]
pub use smallvec_viewstack::ViewStack;
#[cfg(not(feature = "smallvec_viewstack"))]
pub use vec_viewstack::ViewStack;

impl<'a> std::fmt::Debug for ViewStack<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", &self.0)
    }
}

impl<'a> Stack for ViewStack<'a> {
    type Item = SliceBuffer<'a>;

    #[inline]
    fn peek(&self) -> Option<Self::Item> {
        self.0.last().copied()
    }

    #[inline]
    fn peek_mut(&mut self) -> Option<&mut Self::Item> {
        self.0.last_mut()
    }

    #[inline]
    fn pop(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }

    #[inline]
    unsafe fn push_unchecked(&mut self, item: Self::Item) {
        self.0.push(item)
    }
}
