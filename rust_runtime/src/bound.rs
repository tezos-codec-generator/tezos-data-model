use std::fmt::{Debug, Display};

pub enum Bound<T> {
    UpperBound(T),
    LowerBound(T),
}

impl<T: Clone> Clone for Bound<T> {
    fn clone(&self) -> Self {
        match self {
            Self::UpperBound(arg0) => Self::UpperBound(arg0.clone()),
            Self::LowerBound(arg0) => Self::LowerBound(arg0.clone()),
        }
    }
}

impl<T: Copy> Copy for Bound<T> {}

impl<T: Debug> Debug for Bound<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UpperBound(arg0) => f.debug_tuple("UpperBound").field(arg0).finish(),
            Self::LowerBound(arg0) => f.debug_tuple("LowerBound").field(arg0).finish(),
        }
    }
}

impl<T: Display> Display for Bound<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UpperBound(max) => write!(f, "upper bound (:= {})", max),
            Self::LowerBound(min) => write!(f, "lower bound (:= {})", min),
        }
    }
}
