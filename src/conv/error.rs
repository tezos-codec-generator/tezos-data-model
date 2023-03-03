use crate::{parse::{cleanup::{LeftoverState, InvariantError}, error::ParseError}, error::HexConvError};

#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum DecodeError {
    Conv(HexConvError),
    Parse(ParseError),
    Invariant(InvariantError),
    NonEmpty(LeftoverState),
}

impl From<std::convert::Infallible> for DecodeError {
    fn from(_void: std::convert::Infallible) -> Self {
        match _void {}
    }
}

impl From<HexConvError> for DecodeError {
    fn from(err: HexConvError) -> Self {
        Self::Conv(err)
    }
}

impl From<ParseError> for DecodeError {
    fn from(err: ParseError) -> Self {
        Self::Parse(err)
    }
}

impl From<InvariantError> for DecodeError {
    fn from(err: InvariantError) -> Self {
        Self::Invariant(err)
    }
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DecodeError::Conv(err) => {
                write!(f, "hex conversion encountered error: {}", err)
            }
            DecodeError::Parse(err) => {
                write!(f, "parser encountered error: {}", err)
            }
            DecodeError::Invariant(err) => {
                write!(f, "invariant failed during cleanup: {}", err)
            }
            DecodeError::NonEmpty(err) => {
                write!(f, "parser object had non-empty left-over state on cleanup: {:?}", err)
            }
        }
    }
}

impl std::error::Error for DecodeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DecodeError::Conv(err) => Some(err),
            DecodeError::Parse(err) => Some(err),
            DecodeError::Invariant(err) => Some(err),
            DecodeError::NonEmpty(_) => None,
        }
    }
}

pub type DecodeResult<T> = std::result::Result<T, DecodeError>;

#[cfg(test)]
mod test {
    fn dummy<T: Send + Sync>() {}

    #[test]
    fn decode_error_threadsafe() {
        dummy::<super::DecodeError>()
    }

}