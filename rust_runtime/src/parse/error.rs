//! Possible errors encountered during creation or manipulation of
//! Parser objects.

use std::{convert::Infallible, string::FromUtf8Error, fmt::{Display, Formatter, Result}};

use crate::{bound::OutOfRange, error::ConstraintError};

#[derive(Debug, Clone, Copy)]
/// Enumerated type representing error conditions specific to
/// opening, closing, and adhering to context-windows for Parser
/// types.
pub enum WindowErrorKind {
    /// Error case when a method call attempts to open a window
    /// that, if created, would extend beyond the final byte in
    /// the parse-buffer.
    ///
    /// Note that this case can be a fallthrough, and that if a parse-window
    /// happens to exist at the same time, [`OpenWouldExceedWindow`] may
    /// be the reported error.
    OpenWouldExceedBuffer {
        bytes_left: usize,
        request: usize,
    },
    /// Error case when a method call attempts to open a window
    /// that, if created, would be wider than the narrowest
    /// open context-window.
    ///
    /// Note that this error may be reported in cases where the method call
    /// would fail regardless, such as when the requested width would also
    /// exceed successive open windows, or even the entire parse-buffer itself.
    OpenWouldExceedWindow {
        limit: usize,
        request: usize,
    },
    /// Error case when a method call attempts to close the narrowest open
    /// context-window but there are unconsumed bytes remaining within said
    /// window.
    CloseWithResidue {
        residual: usize,
    },
    /// Error case when a method call attempts to close the narrowest open
    /// context-window, but there are no open context-windows to begin with.
    CloseWithoutWindow,
    /// Generic error case where the current offset of a Parser exceeds the bounds
    /// of the narrowest open context-window.
    ///
    /// This case is never expected to be reached, but it is included nonetheless.
    /// It is a critical error in the implementation of a parser if this error is
    /// ever reported.
    OffsetOverflow {
        excess: usize,
    },
}

impl std::fmt::Display for WindowErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            &WindowErrorKind::OpenWouldExceedBuffer { bytes_left, request } => {
                if bytes_left == 0 {
                    write!(f, "Cannot open {}-byte context window: parse-buffer has been fully consumed", request)
                } else {
                    write!(f, "Cannot open {}-byte context window: parse-buffer has only {} bytes remaining", request, bytes_left)
                }
            }
            &WindowErrorKind::OpenWouldExceedWindow { limit, request } => {
                write!(f, "Cannot open {}-byte context window: wider than current window ({} bytes)", request, limit)
            }
            &WindowErrorKind::CloseWithResidue { residual } => {
                write!(f, "Cannot close context window without first consuming {} residual bytes", residual)
            }
            &WindowErrorKind::CloseWithoutWindow => write!(f, "Cannot close context window when there is no context-window to close"),
            &WindowErrorKind::OffsetOverflow { excess } => {
                write!(f, "BUG: detected an offset that exceeds the current limit by {} bytes", excess)
            }
        }
    }
}


/// Enumerated type representing errors in conversion from hex-strings
/// into byte-buffers.
#[derive(Debug, Clone, Copy)]
pub enum ConvError<T> {
    /// `ParityError` indicates the error scenerio in which the parity of the
    /// length of the string we wish to interpret as a hex-encoded byte buffer
    /// is not even, and therefore is malformed.
    ParityError(T),
    /// `HexError` indicates the error scenario in which an aligned two-byte
    /// substring of the string we are converting, is not a valid hexadecimal
    /// encoding of an 8-bit word.
    HexError(T),
}

impl Display for ConvError<()> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Self::ParityError(_) => write!(f, "cannot parse string with odd parity as hexstring"),
            Self::HexError(_) => write!(f, "parsing of hexstring encountered invalid hexadecimal character(s)"),
        }
    }
}

impl Display for ConvError<String> {
    fn fmt(&self, f: &mut Formatter) -> Result {
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

/// Enumerated type representing implementation-specific errors that occur
/// internally when parsing mostly independent of the validity of the request
/// being performed. These should never be encountered unless there is a bug
/// in the implementation of the Parser object itself.
#[derive(Debug, Clone, Copy)]
pub enum InternalErrorKind {
    ConsumeLengthMismatch { expected: usize, actual: usize },
    SliceCoerceFailure,
    NoValidTags,
}

impl Display for InternalErrorKind {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            InternalErrorKind::ConsumeLengthMismatch { expected, actual } => {
                write!(
                    f,
                    "BUG: consume({}) returned slice of length {}",
                    expected, actual
                )
            }
            InternalErrorKind::SliceCoerceFailure => {
                write!(
                    f,
                    "BUG: failed to coerce from byte-slice to fixed-length array"
                )
            }
            InternalErrorKind::NoValidTags => {
                write!(
                    f,
                    "BUG: cannot parse discriminant of enum with no specified valid values"
                )
            }
        }
    }
}

/// Enumerated type representing contextually invalid results obtained from otherwise
/// succesfully executed method calls to a Parser object. These typically indicate that
/// the actual byte content of the buffer differs from the byte content that is considered
/// valid in the context imposed by a particular parse method call or combination thereof.
#[derive(Debug, Clone)]
pub enum ExternalErrorKind {
    /// Error scenario in which a coercion from `&[u8]` to `String` performed on the result
    /// of a `consume` operation could not be performed for the specified reason (`FromUtf8Error`).
    UncoercableString(FromUtf8Error),
    /// Error scenario in which an integral value parsed from the buffer happened to fall outside
    /// of the valid range of a RangedInt type.
    IntRangeViolation(OutOfRange<i64>),
    /// Error scenario in which a double-precision IEEE float parsed from the buffer happened to fall
    /// outside of the valid range of a RangedFloat type.
    FloatRangeViolation(OutOfRange<f64>),
    /// Error scenario in which a trivial type-conversion could not be performed without implicitly
    /// violating a type-level (schema-level) constraint in the target type.
    ConstraintViolation(ConstraintError),
}

impl From<FromUtf8Error> for ExternalErrorKind {
    fn from(err: FromUtf8Error) -> Self {
        Self::UncoercableString(err)
    }
}

impl From<OutOfRange<i64>> for ExternalErrorKind {
    fn from(err: OutOfRange<i64>) -> Self {
        Self::IntRangeViolation(err)
    }
}

impl From<OutOfRange<f64>> for ExternalErrorKind {
    fn from(err: OutOfRange<f64>) -> Self {
        Self::FloatRangeViolation(err)
    }
}

impl From<ConstraintError> for ExternalErrorKind {
    fn from(err: ConstraintError) -> Self {
        Self::ConstraintViolation(err)
    }
}

impl Display for ExternalErrorKind {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            ExternalErrorKind::UncoercableString(err) => {
                write!(
                    f,
                    "parsed byte-array could not be coerced to String: {}",
                    err
                )
            }
            ExternalErrorKind::IntRangeViolation(x) => {
                write!(f, "{}", x)
            }
            ExternalErrorKind::FloatRangeViolation(x) => {
                write!(f, "{}", x)
            }
            ExternalErrorKind::ConstraintViolation(x) => {
                write!(f, "{}", x)
            }
        }
    }
}

pub trait TagType
where
    Self: std::fmt::Debug + Display + Clone + Copy + PartialEq + Eq + std::fmt::LowerHex,
{
    fn promote(val: TagError<Self>) -> TagErrorKind;
}

impl TagType for u8 {
    fn promote(val: TagError<Self>) -> TagErrorKind {
        TagErrorKind::TagU8(val)
    }
}

impl TagType for u16 {
    fn promote(val: TagError<Self>) -> TagErrorKind {
        TagErrorKind::TagU16(val)
    }
}
impl TagType for u32 {
    fn promote(val: TagError<Self>) -> TagErrorKind {
        TagErrorKind::TagU30(val)
    }
}

#[derive(Debug, Clone)]
pub struct TagError<T>
where
    T: TagType,
{
    actual: T,
    for_type: Option<String>,
    expected: Option<Vec<T>>,
}

impl<T> TagError<T>
where
    T: Into<TagError<T>> + TagType,
{
    pub fn new(actual: T, for_type: Option<String>, expected: Option<Vec<T>>) -> Self {
        let mut ret: Self = actual.into();
        if let Some(for_type) = for_type {
            (&mut ret.for_type).replace(for_type);
        }
        if let Some(expected) = expected {
            (&mut ret.expected).replace(expected);
        }
        ret
    }
}

impl<T: TagType> From<T> for TagError<T> {
    fn from(actual: T) -> Self {
        Self {
            actual,
            for_type: None,
            expected: None,
        }
    }
}

impl<T> Display for TagError<T>
where
    T: TagType,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "unexpected discriminant {:#0width$x} for enum-type {}",
            &self.actual,
            self.for_type.as_ref().unwrap_or(&String::from("<unknown>")),
            width = std::mem::size_of::<T>() * 2
        )
    }
}

#[derive(Debug, Clone)]
pub enum TagErrorKind {
    TagU8(TagError<u8>),
    TagU16(TagError<u16>),
    TagU30(TagError<u32>),
}

impl Display for TagErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            TagErrorKind::TagU8(x) => std::fmt::Display::fmt(x, f),
            TagErrorKind::TagU16(x) => std::fmt::Display::fmt(x, f),
            TagErrorKind::TagU30(x) => std::fmt::Display::fmt(x, f),
        }
    }
}

impl<T: TagType> From<TagError<T>> for TagErrorKind {
    fn from(val: TagError<T>) -> Self {
        TagType::promote(val)
    }
}

/// Enumerated type encapsulating all possible error conditions that can be raised by
/// operations that attempt to create or manipulate Parser objects
#[derive(Debug, Clone)]
pub enum ParseError {
    /// Error encountered when opening, closing, or adhering to context windows.
    WindowError(WindowErrorKind),
    /// Internal error indicating a bug in the implementation
    InternalError(InternalErrorKind),
    /// External error indicating a contextually invalid parse-result
    ExternalError(ExternalErrorKind),
    /// Attempted consume call would violate the absolute or contextually
    /// restricted bounds of the parse-buffer
    BufferOverflow {
        buflen: usize,
        offset: usize,
        requested: usize,
    },
    /// Byte parsed could not be interpreted as a valid boolean
    InvalidBoolean(u8),
    /// Byte parsed could not be interpreted as a valid discriminant for an enumerated type
    InvalidTag(TagErrorKind),
    /// Supposedly self-terminating byte-sequence failed to terminate before reaching end of buffer
    NonTerminating(Vec<u8>),
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            ParseError::WindowError(err) => {
                write!(f, "Context-window error: {}", err)
            }
            ParseError::BufferOverflow {
                buflen,
                offset,
                requested,
            } => {
                write!(f, "cannot increment offset by {} bytes (currently at byte {} in buffer of length {})", requested, offset, buflen)
            }
            ParseError::InternalError(err) => {
                write!(f, "Internal error: {}", err)
            }
            ParseError::ExternalError(err) => {
                write!(f, "External error: {}", err)
            }
            ParseError::InvalidBoolean(byte) => {
                write!(f, "expected boolean := (0xff | 0x00), got 0x{:02x}", byte)
            }
            ParseError::InvalidTag(err) => {
                write!(f, "invalid tag: {}", err)
            }
            ParseError::NonTerminating(buf) => {
                write!(f, "self-terminating codec cut off (end-of-window encountered before terminating condition met): `{}`", crate::util::hex_of_bytes(buf))
            }
        }
    }
}

impl From<Infallible> for ParseError {
    fn from(_: Infallible) -> Self {
        unreachable!()
    }
}

impl<T> From<T> for ParseError
where
    ExternalErrorKind: From<T>,
{
    fn from(err: T) -> Self {
        Self::ExternalError(ExternalErrorKind::from(err))
    }
}

impl From<WindowErrorKind> for ParseError
{
    fn from(err: WindowErrorKind) -> Self {
        Self::WindowError(err)
    }
}


pub type ParseResult<T> = std::result::Result<T, ParseError>;