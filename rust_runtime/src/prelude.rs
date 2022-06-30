//! Assorted imports to use
//! when renaming runtime types with the possibility of
//!

pub mod stable_names {
    //! API scaffolding to allow for more flexible renaming of primary internal
    //! type until these changes are stabilized.

    /// Alias for [`FixedBytes<N>`] under its previous name
    pub type ByteString<const N: usize> = crate::fixed::bytes::FixedBytes<N>;

    /// Alias for [`FixedString<N>`] under its previous name
    pub type CharString<const N: usize> = crate::fixed::string::FixedString<N>;
}

#[doc(inline)]
pub use stable_names::*;