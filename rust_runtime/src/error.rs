use std::error::Error;
use std::fmt::{Debug, Display};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum ConstraintError {
    /// Error case representing a violation of type-level cardinality constraints
    /// on a bounded sequence. Note that this error may not reflect the true length
    /// of the invalid conversion, as it may have been returned from a parse operation
    /// that short-circuited when it did not terminate its parse-loop after [limit]
    /// elements were already added.
    TooManyElements { limit: usize, actual: usize },
    /// Error case representing a violation of type-level cardinality constraints
    /// on an exact-length sequence, whether too few or too many.
    ConstantLengthViolation { expected: usize, actual: usize },
    /// Error case representing a violation of type-level serialization-width constraints
    /// on a size-bounded value.
    TooManyBytes { limit: usize, actual: usize },
}

impl Display for ConstraintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintError::TooManyElements { limit, actual } => write!(
                f,
                "schema-level cardinality-constraint violation: max is {}, found {}",
                limit, actual
            ),
            ConstraintError::ConstantLengthViolation { expected, actual } => write!(
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

/// Enumerated type representing errors in conversion from hex-strings
/// into byte-buffers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub enum ConvError<T> {
    /// Constructor `ParityError` indicates the error scenario in which the parity of the
    /// length of the string we wish to interpret as a hex-encoded byte buffer
    /// is not even, and therefore is malformed.
    ParityError(T),
    /// `HexError` indicates the error scenario in which an aligned two-byte
    /// substring of the string we are converting, is not a valid hexadecimal
    /// encoding of an 8-bit word.
    HexError(T),
}

impl ConvError<&'_ str>
{
    pub fn to_owned(self) -> ConvError<String> {
        match self {
            ConvError::ParityError(src) => ConvError::ParityError(src.to_owned()),
            ConvError::HexError(src) => ConvError::HexError(src.to_owned()),
        }
    }
}

impl Display for ConvError<()> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ParityError(_) => write!(f, "cannot parse string with odd parity as hexstring"),
            Self::HexError(_) => write!(
                f,
                "parsing of hexstring encountered invalid hexadecimal character(s)"
            ),
        }
    }
}

impl Display for ConvError<&'_ str> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ParityError(s) => {
                write!(
                    f,
                    "input string has odd parity ({}) (expected even): '{}'",
                    s.len(),
                    s
                )
            }
            Self::HexError(s) => {
                write!(
                    f,
                    "input string contains non-hex two-byte aligned substring: '{}'",
                    s
                )
            }
        }
    }
}

impl Display for ConvError<String> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ParityError(s) => {
                write!(
                    f,
                    "input string has odd parity ({}) (expected even): '{}'",
                    s.len(),
                    s
                )
            }
            Self::HexError(s) => {
                write!(
                    f,
                    "input string contains non-hex two-byte aligned substring: '{}'",
                    s
                )
            }
        }
    }
}

impl Error for ConvError<()> {}
impl Error for ConvError<&'_ str> {}
impl Error for ConvError<String> {}

/// Error type representing invalidity of (numeric) values
/// based on an implicit lower and upper bound.
///
/// * `Underflow {..}` contains the illegal value in question, as well as the lower bound it falls below
/// * `Overflow {..}` contains the illegal value in question, as well as the upper bound it falls above
///
/// Because the source type of the value we are attempting to confine to the range
/// may be wider than the type used to represent the range bounds, a generic type
/// parameter `Ext` is used to indicate the type we have used to encapsulate the values
/// of both the input and the range bounds, and should have the property that both
/// of those two types can be converted infallibly to `Ext` without perturbing
/// the relative ordering of the values; hence the `PartialOrd` bound on `Ext`.
/// Furthermore, it is not intended that this error type represent any non-numeric
/// bounds or values, and therefore the `Copy` bound is also mandated here rather
/// than just at associated function sites.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BoundsError<Ext> {
    Underflow { min: Ext, val: Ext },
    Overflow { max: Ext, val: Ext },
    InvalidBounds { min: Ext, max: Ext },
    FailedConversion,
}

impl<Ext> BoundsError<Ext> {
    /// Checks that a value `val falls into the specified range `[min, max]`, returning
    /// `Ok(val)` if this condition holds.
    ///
    /// If `val < min`, returns `Err(BoundsError::Underflow { .. })`
    ///
    /// If `val > max`, returns `Err(BoundsError::Overflow { .. })`
    ///
    /// As the type of `val` can be different from the type of `min` and `max`,
    /// this comparison is handled by first converting all three values to
    /// the external numeric type `Ext`.
    ///
    /// Attempts to 1Restricts input values of a numeric type `T: Into<Ext> + Copy>`
    /// into the range defined by a lower and upper bound of type `U: Into<Ext>`.
    ///
    /// If the provided value `x` is within the range bounds, this method leaves it unmodified
    /// and returns `Ok(x)`;
    /// otherwise, returns an `Err` containing the appropriate `OutOfRange` variant.
    ///
    pub fn restrict<T, U>(val: T, min: U, max: U) -> Result<T, Self>
    where
        Ext: PartialOrd + Copy,
        T: std::convert::TryInto<Ext> + Copy,
        U: Into<Ext> + PartialOrd,
    {
        let min_ext: Ext = min.into();
        let max_ext: Ext = max.into();
        if let Ok(val_ext) = val.try_into() {
            if val_ext >= min_ext {
                if val_ext <= max_ext {
                    Ok(val)
                } else if min_ext > max_ext {
                    Err(Self::InvalidBounds {
                        min: min_ext,
                        max: max_ext,
                    })
                } else {
                    Err(Self::Overflow {
                        max: max_ext,
                        val: val_ext,
                    })
                }
            } else if min_ext > max_ext {
                Err(Self::InvalidBounds {
                    min: min_ext,
                    max: max_ext,
                })
            } else {
                Err(Self::Underflow {
                    min: min_ext,
                    val: val_ext,
                })
            }
        } else {
            Err(Self::FailedConversion)
        }
    }
}

impl BoundsError<f64> {
    pub fn restrict_float<T>(val: T, min: f64, max: f64) -> Result<f64, Self>
    where
        f64: From<T>,
    {
        if min <= max {
            let val: f64 = val.into();
            if val >= min {
                if val <= max {
                    Ok(val)
                } else {
                    Err(Self::Overflow { max, val })
                }
            } else {
                Err(Self::Underflow { min, val })
            }
        } else {
            Err(Self::InvalidBounds { min, max })
        }
    }
}

impl<Ext: Display> Display for BoundsError<Ext> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BoundsError::Underflow { ref min, ref val } => {
                write!(f, "provided value {} less than minimum bound {}", val, min)
            }
            BoundsError::Overflow { ref max, ref val } => {
                write!(
                    f,
                    "provided value {} greater than maximum bound {}",
                    val, max
                )
            }
            BoundsError::InvalidBounds { ref min, ref max } => {
                write!(
                    f,
                    "min <= max is not satisfied for the range ({},{})",
                    min, max
                )
            }
            BoundsError::FailedConversion => {
                write!(
                    f,
                    "conversion to external type {} failed during ranged value bounds-checking",
                    std::any::type_name::<Ext>(),
                )
            }
        }
    }
}

impl<Ext: Display + Debug> std::error::Error for BoundsError<Ext> {}
