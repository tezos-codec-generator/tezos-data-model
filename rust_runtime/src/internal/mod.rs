//! Low-level logic used throughout this crate
//!
//! This module serves as a general heading for assorted modules
//! that are designed primarily for library-internal use, and do not
//! have an immediately obvious alternate module to live under.
//!
//! In another context these definitions might be imported from one or more
//! external crates, but they are either trivial enough to not merit the cost
//! of adding a dependency, or niche enough that it is most likely impossible
//! to find an exact analogue in another library.
//!
//! There are no top-level definitions in this module, save for the re-exports
//! of the `SplitVec` type from the `splitvec` submodule, and the `Stack` trait
//! from the `stack` submodule. Additionally, the `offset` submodule contains
//! relevant definitions to the mutable contextually limited offset-tracking
//! of vector-oriented `Parser` types, namely `ByteParser` and its
//! cousin `MemoParser`.

pub(crate) mod offset;
pub(crate) mod splitvec;
pub(crate) mod stack;
pub(crate) mod view;

pub(crate) use splitvec::SplitVec;
pub(crate) use stack::Stack;
