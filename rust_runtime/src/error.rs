use std::error::Error;
use std::fmt::Display;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum ConstraintError {
    /// Error case representing a violation of type-level cardinality constraints
    /// on a bounded sequence. Note that this error may not reflect the true length
    /// of the invalid conversion, as it may have been returned from a parse operation
    /// that short-circuited when it did not terminate its parse-loop after [limit]
    /// elements were already added.
    TooManyElements {
        limit: usize,
        actual: usize,
    },
    /// Error case representing a violation of type-level cardinality constraints
    /// on an exact-length sequence, whether too few or too many.
    InexactCardinality {
        expected: usize,
        actual: usize,
    },
    /// Error case representing a violation of type-level serialization-width constraints
    /// on a size-bounded value.
    TooManyBytes {
        limit: usize,
        actual: usize,
    },
}

impl Display for ConstraintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintError::TooManyElements { limit, actual } => write!(
                f,
                "schema-level cardinality-constraint violation: max is {}, found {}",
                limit, actual
            ),
            ConstraintError::InexactCardinality { expected, actual } => write!(
                f,
                "schema-level cardinality-constraint violation: expected {}, found {}",
                expected, actual
            ),
            ConstraintError::TooManyBytes { limit, actual } => write!(
                f,
                "schema-level bytewidth-constraint violation: max is {}, found {}",
                limit, actual
            ),
        }
    }
}

impl Error for ConstraintError {}
