//! General error types
//!
//! This module contains
//! though not comprehensiv
//!
//! which may
//!
//! moved into a dedicated module heading.

use std::convert::Infallible;
use std::error::Error;
use std::fmt::{Debug, Display};
use std::num::TryFromIntError;
use std::ops::Sub;

/// Enumerated error type for failures related to schema constructs
/// that impose a check on the byte-width on their prospective values.
///
/// Structurally similar to [`LengthError`], an analoguous error-type
/// relating to the number of elements in a collection-type, rather than
/// the number of bytes in a potentially opaque schema type.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug)]
pub enum WidthError {
    /// Restriction on maximum byte-width exceeded
    TooWide { limit: usize, actual: usize },
    /// Requirement of precise byte-width not satisfied
    WrongWidth { exact: usize, actual: usize },
    /// Restriction to set of allowable byte-widths not satisfied
    InvalidWidth {
        valid: &'static [usize],
        actual: usize,
    },
}

impl Display for WidthError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WidthError::TooWide { limit, actual } => {
                write!(f, "{actual}-byte value exceeded limit of {limit} bytes")
            }
            WidthError::WrongWidth { exact, actual } => {
                write!(
                    f,
                    "{actual}-byte value violated requirement of {exact} bytes"
                )
            }
            WidthError::InvalidWidth { valid, actual } => {
                write!(
                    f,
                    "byte-length {actual} of value not in set {valid:?} of valid lengths"
                )
            }
        }
    }
}

impl Error for WidthError {}

/// Enumerated error type for failures related to schema constructs
/// that impose a check on the element-count of their prospective
/// values, which are typically collection types.
///
/// Structurally similar to [`WidthError`], an analogous error-type
/// relating to the byte-width of a potentially opaque schema type,
/// rather than the number of elements in a collection-type.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug)]
pub enum LengthError {
    /// Restriction on maximum element-count exceeded
    TooLong { limit: usize, actual: usize },
    /// Requirement of precise element-count not satisfied
    WrongLength { exact: usize, actual: usize },
}

impl Display for LengthError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LengthError::TooLong { limit, actual } => {
                write!(
                    f,
                    "{actual}-element value exceeded limit of {limit} elements"
                )
            }
            LengthError::WrongLength { exact, actual } => {
                write!(
                    f,
                    "{actual}-element value violated requirement of {exact} elements"
                )
            }
        }
    }
}

impl Error for LengthError {}

/// Error type representing all possible conditions for invalidity
/// encountered when attempting to parse a string-type as a series
/// of hex-encoded bytes.
#[derive(Clone, PartialEq, Eq, Ord, PartialOrd)]
pub enum HexConvError {
    /// Error case for odd-length strings
    OddParity(String),
    /// Error case for strings containing non-hex characters,
    /// i.e. anything not in `[0-9a-fA-F]`.
    NonHex(String),
}

impl Debug for HexConvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OddParity(invalid) => {
                write!(f, "non-even length-parity for string `{}`", invalid)
            }
            Self::NonHex(invalid) => write!(f, "non-hex character found in string `{}`", invalid),
        }
    }
}

impl Display for HexConvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OddParity(_) => {
                write!(f, "hex-conversion failed on odd-length string")
            }
            Self::NonHex(_) => {
                write!(f, "hex-conversion failed on non-hex character")
            }
        }
    }
}

impl Error for HexConvError {}

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
pub enum BoundsError<Ext: Debug> {
    Underflow { min: Ext, val: Ext },
    Overflow { max: Ext, val: Ext },
    InvalidBounds { min: Ext, max: Ext },
    IllegalNegative { min: Ext, val: Ext },
    Failed(TryFromIntError),
}

impl<Ext: Debug> From<Infallible> for BoundsError<Ext> {
    fn from(_void: Infallible) -> Self {
        match _void {}
    }
}

impl<Ext: Debug> From<TryFromIntError> for BoundsError<Ext> {
    fn from(err: TryFromIntError) -> Self {
        Self::Failed(err)
    }
}

impl<Ext: Debug> BoundsError<Ext> {
    /// Checks that a value `val` falls into the specified range `[min, max]`, returning
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
    /// # Boundary Case (`min > 0`)
    ///
    /// If `min > 0`, it is implicitly unsound for `val < 0`, and otherwise
    /// `val` will be interpreted as a non-negative offset from `min`. It is
    /// then subject to the same validation (`MIN <= MAX` and `val <= MAX - MIN`),
    /// but is not mapped into the specified range when it is returned.
    pub fn restrict<T, U>(val: T, min: U, max: U) -> Result<T, Self>
    where
        Ext: PartialOrd + Copy + Sub<Output = Ext>,
        T: std::convert::TryInto<Ext> + Copy,
        U: Into<Ext> + PartialOrd,
        i32: Into<Ext>,
        BoundsError<Ext>: From<T::Error>,
    {
        let min_ext: Ext = min.into();
        let max_ext: Ext = max.into();
        let val_ext = val.try_into()?;
        if min_ext > (0).into() {
            if val_ext < (0).into() {
                return Err(BoundsError::IllegalNegative {
                    min: min_ext,
                    val: val_ext,
                });
            } else if max_ext < min_ext {
                return Err(Self::InvalidBounds {
                    min: min_ext,
                    max: max_ext,
                });
            } else if val_ext > max_ext - min_ext {
                return Err(Self::Overflow {
                    max: max_ext - min_ext,
                    val: val_ext,
                });
            } else {
                return Ok(val);
            }
        } else if val_ext >= min_ext {
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

impl<Ext: Debug + Display> Display for BoundsError<Ext> {
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
            BoundsError::Failed(err) => {
                write!(f, "could not convert for bounds-checking: {}", err)
            }
            BoundsError::IllegalNegative { ref min, ref val } => {
                write!(
                    f,
                    "negative value {} cannot be interpreted as a positive offset from minimum bound {} > 0",
                    val,
                    min
                )
            }
        }
    }
}

impl<Ext: Display + Debug> std::error::Error for BoundsError<Ext> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Failed(err) => Some(err),
            _ => None,
        }
    }
}
