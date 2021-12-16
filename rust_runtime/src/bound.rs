use std::{fmt::{Debug, Display}};

use crate::parse::errors::{ParseError, ExternalErrorKind};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum OutOfRange<Ext: Copy> {
    Underflow { min: Ext, val: Ext },
    Overflow { max: Ext, val: Ext },
}

impl<Ext: Copy + PartialOrd> OutOfRange<Ext> {
    /// Restricts input values of an integral type `T: Into<i64> + Copy>`
    /// into the range defined by a lower and upper bound of type `U: Into<i64>`.
    ///
    /// If the provided value is within the range bounds, returns that value wrapped in an `Ok`
    /// constructor; otherwise returns an `Err` containing the appropriate `OutOfRange` variant.
    ///
    pub fn restrict<T, U>(x: T, min: U, max: U) -> Result<T, Self>
    where
        T: Into<Ext> + Copy,
        U: Into<Ext>,
    {
        let min_ext: Ext = min.into();
        let max_ext: Ext = max.into();
        let val: Ext = x.into();
        if val < min_ext {
            Err(Self::Underflow { min: min_ext, val })
        } else if val > max_ext {
            Err(Self::Overflow { max: max_ext, val })
        } else {
            Ok(x)
        }
    }
}

impl<Ext: Display + Copy> Display for OutOfRange<Ext> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            &OutOfRange::Underflow { min, val } => write!(
                f,
                "Provided value (:= {}) less than RangedInt minimum bound (:= {})",
                val, min
            ),
            &OutOfRange::Overflow { max, val } => write!(
                f,
                "Provided value (:= {}) greater than RangedInt maximum bound (:= {})",
                val, max
            ),
        }
    }
}

impl Into<ParseError> for OutOfRange<i64> {
    fn into(self) -> ParseError {
        ParseError::ExternalError(ExternalErrorKind::IntRangeViolation(self))
    }
}

impl Into<ParseError> for OutOfRange<f64> {
    fn into(self) -> ParseError {
        ParseError::ExternalError(ExternalErrorKind::FloatRangeViolation(self))
    }
}
