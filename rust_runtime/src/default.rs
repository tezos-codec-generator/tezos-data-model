
/// Generates boilerplate code to simulate default-valued record fields
///
/// Generative macro used in codecs transcribed from schemas containing
/// records with implicitly default-valued fields.
///
/// Such fields are
/// represented in binary as if they were optional, but in terms of the actual
/// encoding semantics, a single null byte for the field decodes to some
/// schema-specific default value, and said value should typically be encoded
/// back as `0x00`, as the intent of default-valued fields is to save overhead
/// when encoding the common default value.
///
/// # Design
///
/// The approach taken by this macro is to define two main items:
///   * A `static` holding the default value of the field in question
///   * A newtype around the underlying type of the field in question
///
/// The newtype provides methods for coercion to and from its underlying type,
/// as well as from [`Option<T>`] around the underlying type. It implements
/// the `Default` trait directly, using the associated static as the
/// return value of the `default` method. If the underlying type
/// happens to have an implementation of `Default`, it is ignored.
///
/// A default-valued instance of the newtype is
///
///
/// Note that because the code generation process can neither correctly
/// represent the OCaml value specified as the default, such that it
/// can be written as a constant expression, nor can the rhs of even
/// an immutable `static` definition be non-constant, a shortcut is taken
/// using the `lazy_static` macro (from the crate `lazy_static`), which
/// is re-exported by this crate so that the `dft` macro can be used
/// as-is without non-obvious extra dependencies.
///
///
///
/// invocation (see the Syntax section for more information)
/// using a newtype pattern around the nominal value of the field in question,
/// with separate implementations of [`Encode`], [`Decode`], and [`Estimate`]
/// that perform the same value-specific optimizations as interoperable
/// OCaml code using the `data-encoding` implementation would.
///
/// In order to achieve this, this macro creates a non-`const` but otherwise immutable
/// static (using a crate re-export of `lazy_static`)
///
/// # Syntax
///
/// # Semantics
///
///
///
#[macro_export]
macro_rules! dft {
    (@memo create $id:ident : $t:ty = $x:expr) => {
        $crate::lazy_static! {
            pub static ref $id : $t = <$t as $crate::Decode>::decode($crate::hex!($x));
        }
    };
    ($id:ident [$tmp:ident] ($t:ty = $dft:expr)) => {
        #[derive(Debug, Clone, PartialEq, PartialOrd, Hash)]
        #[repr(transparent)]
        pub struct $id($t);

        impl $id {
            #[inline(always)]
            pub fn from_inner(val: $t) -> Self {
                Self(val)
            }

            #[inline(always)]
            pub fn into_inner(self) -> $t {
                self.0
            }

            #[inline(always)]
            pub fn is_default(&self) -> bool {
                self.0 == *$tmp
            }
        }

        dft!(@memo create $tmp : $t = $dft);

        impl ::std::default::Default for $id {
            fn default() -> Self {
                Self($tmp.clone())
            }
        }

        impl From<Option<$t>> for $id {
            fn from(val: Option<$t>) -> $id {
                match val {
                    Some(x) => Self(x),
                    None => Self::default(),
                }
            }
        }

        impl From<$t> for $id {
            fn from(val: $t) -> $id {
                Self(val)
            }
        }

        impl $crate::Encode for $id {
            #[inline(always)]
            fn write_to<U: $crate::Target>(&self, buf: &mut U) -> usize {
                match &self.0 {
                    x if *x == *$tmp => <Option<$t> as $crate::Encode>::write_to(&None, buf),
                    x => {
                        buf.push_one(0xffu8) + <$t as $crate::Encode>::write_to(x, buf)
                    }
                }
            }
        }

        impl $crate::Decode for $id {
            fn parse<P: $crate::Parser>(p: &mut P) -> $crate::ParseResult<Self> {
                Ok(<Option<$t> as $crate::Decode>::parse(p)?.into())
            }
        }

        impl $crate::Estimable for $id {
            const KNOWN : Option<usize> = None;

            fn unknown(&self) -> usize {
                match &self.0 {
                    x if *x == *$tmp => 1,
                    x => 1 + <$t as $crate::Estimable>::estimate(x),
                }
            }
        }
    };
}