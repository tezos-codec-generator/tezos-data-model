//! Utility module related to the type [`HexString`], which supports infallible
//! conversions to and from byte-buffer types (e.g. `Vec<u8>`, `&[u8]`) and
//! validated (i.e. fallible) conversions from [`str`]-based types (e.g. `String`)

use super::error::ConvError::{self, HexError, ParityError};
use crate::{builder::Builder, util::hex_of_bytes};
use std::{borrow::Borrow, convert::TryFrom, iter::FromIterator, vec::IntoIter};

/// Newtype representing byte-arrays that are parsed from and displayed as
/// hexadecimally encoded `String` values, but stored in memory as byte-buffers
/// representing the individual words parsed from the String.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct HexString {
    words: Vec<u8>,
}

impl AsRef<Vec<u8>> for HexString {
    fn as_ref(&self) -> &Vec<u8> {
        &self.words
    }
}

impl AsMut<Vec<u8>> for HexString {
    fn as_mut(&mut self) -> &mut Vec<u8> {
        &mut self.words
    }
}

impl AsRef<[u8]> for HexString {
    fn as_ref(&self) -> &[u8] {
        self.words.as_ref()
    }
}

impl AsMut<[u8]> for HexString {
    fn as_mut(&mut self) -> &mut [u8] {
        self.words.as_mut()
    }
}

impl<T: AsMut<Vec<u8>>> std::ops::Add<T> for HexString {
    type Output = HexString;

    fn add(mut self, mut rhs: T) -> Self::Output {
        self.words.append(rhs.as_mut());
        self
    }
}

impl<T: AsMut<Vec<u8>>> std::ops::AddAssign<T> for HexString {
    fn add_assign(&mut self, mut rhs: T) {
        self.words.append(rhs.as_mut());
    }
}

macro_rules! impl_from {
    ( $src:ty ) => {
        impl From<$src> for HexString {
            fn from(words: $src) -> Self {
                Self { words }
            }
        }
    };
    ( $src:ty, $meth:ident ) => {
        impl From<$src> for HexString {
            fn from(src: $src) -> Self {
                Self { words: src.$meth() }
            }
        }
    };
    ( $lt:lifetime, $src:ty, $meth:ident ) => {
        impl<$lt> From<$src> for HexString {
            fn from(src: $src) -> Self {
                Self { words: src.$meth() }
            }
        }
    };
}

impl_from!(Vec<u8>);
impl_from!(&[u8], to_vec);
impl_from!(Box<[u8]>, to_vec);
impl_from!(std::rc::Rc<[u8]>, to_vec);
impl_from!(std::sync::Arc<[u8]>, to_vec);
impl_from!(std::borrow::Cow<'_, [u8]>, to_vec);

impl FromIterator<u8> for HexString {
    fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> Self {
        Self {
            words: iter.into_iter().collect::<Vec<u8>>(),
        }
    }
}

fn validate_hex<T: Borrow<str>>(s: &T) -> Result<Vec<u8>, ConvError<()>> {
    crate::util::bytes_of_hex(&s.borrow())
}

macro_rules! impl_try_from {
    ( $src:ty ) => {
        impl TryFrom<$src> for HexString {
            type Error = ConvError<String>;

            fn try_from(s: $src) -> Result<Self, Self::Error> {
                match validate_hex(&s) {
                    Ok(words) => Ok(HexString { words }),
                    Err(HexError(())) => Err(HexError(s.to_string())),
                    Err(ParityError(())) => Err(ParityError(s.to_string())),
                }
            }
        }
    };
}

impl_try_from!(&str);
impl_try_from!(String);

impl Into<Vec<u8>> for HexString {
    fn into(self) -> Vec<u8> {
        self.words
    }
}

/// Macro for converting a string literal into a HexString, which panics if the conversion
/// cannot be performed due to invalidity of the source string.
#[macro_export]
macro_rules! hex {
    ($s : expr) => {{
        <$crate::parse::hexstring::HexString as std::convert::TryFrom<&str>>::try_from($s)
            .expect("hex! macro encountered error")
    }};
}

impl Builder for HexString {
    type Segment = Vec<u8>;
    type Final = Self;

    fn promote(seg: Self::Segment) -> Self {
        Self { words: seg }
    }

    fn word(b: u8) -> Self {
        Self { words: vec![b] }
    }

    fn words<const N: usize>(b: [u8; N]) -> Self {
        Self { words: b.to_vec() }
    }

    fn finalize(self) -> Self {
        self
    }

    fn into_vec(self) -> Vec<u8> {
        self.words
    }

    fn len(&self) -> usize {
        self.words.len()
    }
}

impl std::str::FromStr for HexString {
    type Err = super::error::ConvError<String>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl PartialEq<&str> for HexString {
    fn eq(&self, other: &&str) -> bool {
        <HexString as PartialEq<HexString>>::eq(self, &other.parse().unwrap())
    }
}

impl PartialEq<String> for HexString {
    fn eq(&self, other: &String) -> bool {
        <HexString as PartialEq<HexString>>::eq(self, &other.parse().unwrap())
    }
}

impl PartialEq<HexString> for String {
    fn eq(&self, other: &HexString) -> bool {
        <HexString as PartialEq<String>>::eq(other, &self)
    }
}

impl PartialEq<HexString> for &str {
    fn eq(&self, other: &HexString) -> bool {
        <HexString as PartialEq<&str>>::eq(other, self)
    }
}

impl HexString {
    /// Destructures the HexString wrapper into the actual vector it encloses
    pub fn to_vec(self) -> Vec<u8> {
        self.words
    }

    /// Returns a hexidecimally encoded `String` matching the byte sequence of a borrowed HexString
    pub fn as_hex(&self) -> String {
        hex_of_bytes(&self.words)
    }
}

impl std::fmt::Display for HexString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        String::fmt(&self.as_hex(), f)
    }
}

impl IntoIterator for HexString {
    type Item = u8;

    type IntoIter = IntoIter<u8>;

    fn into_iter(self) -> Self::IntoIter {
        self.words.into_iter()
    }
}
