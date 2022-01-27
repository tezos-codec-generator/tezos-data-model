use std::fmt::{Debug, Display};

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
pub enum OutOfRange<Ext> {
    Underflow { min: Ext, val: Ext },
    Overflow { max: Ext, val: Ext },
}

impl<Ext> OutOfRange<Ext> {
    /// Restricts input values of a numeric type `T: Into<Ext> + Copy>`
    /// into the range defined by a lower and upper bound of type `U: Into<Ext>`.
    ///
    /// If the provided value `x` is within the range bounds, this method leaves it unmodified
    /// and returns `Ok(x)`;
    /// otherwise, returns an `Err` containing the appropriate `OutOfRange` variant.
    ///
    pub fn restrict<T, U>(x: T, min: U, max: U) -> Result<T, Self>
    where
        Ext: PartialOrd + Copy,
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

impl<Ext: Display> Display for OutOfRange<Ext> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OutOfRange::Underflow { ref min, ref val } => write!(
                f,
                "Provided value (:= {}) less than RangedInt minimum bound (:= {})",
                val, min
            ),
            OutOfRange::Overflow { ref max, ref val } => write!(
                f,
                "Provided value (:= {}) greater than RangedInt maximum bound (:= {})",
                val, max
            ),
        }
    }
}
