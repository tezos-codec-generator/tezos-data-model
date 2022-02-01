pub trait FixedLength {
    const LEN: usize;
}

macro_rules! fix_length {
    ($n:expr, $($x:ty),+) => {
        $(impl FixedLength for $x {
            const LEN : usize = $n;
        })+
    };
}

fix_length!(0, ());
fix_length!(1, u8, i8, bool);
fix_length!(2, u16, i16);
fix_length!(4, u32, i32);
fix_length!(8, i64, u64);

impl<T: FixedLength, const N: usize> FixedLength for [T; N] {
    const LEN: usize = N * T::LEN;
}

pub trait ScalarLength {
    const FIXED: Option<usize> = None;

    type Elem: FixedLength;

    const PER_ELEM: usize = <Self::Elem as FixedLength>::LEN;

    fn n_elems(&self) -> usize;
}

impl<T: FixedLength> ScalarLength for T {
    const FIXED: Option<usize> = Some(T::LEN);

    type Elem = Self;

    fn n_elems(&self) -> usize {
        1
    }
}

pub trait Estimable {
    const KNOWN: Option<usize>;

    fn unknown(&self) -> usize;

    fn len(&self) -> usize {
        Self::KNOWN.unwrap_or_else(|| self.unknown())
    }
}

impl<T> Estimable for T
where
    T: ScalarLength,
{
    const KNOWN: Option<usize> = Self::FIXED;

    fn unknown(&self) -> usize {
        self.n_elems() * Self::PER_ELEM
    }
}

impl<T> Estimable for Option<T>
where
    T: Estimable,
{
    const KNOWN: Option<usize> = None;

    fn unknown(&self) -> usize {
        match self {
            &None => 1,
            Some(x) => 1 + x.len(),
        }
    }
}


macro_rules! impl_scalar_len {
    ( $elt:ident ; $( $x:ty ),+ ) =>  {
        $(
            impl<$elt: FixedLength> ScalarLength for $x {
                type Elem = $elt;
                fn n_elems(&self) -> usize {
                    self.len()
                }
            }
        )+
    };
    ( $( $x:ty ),+ ) =>  {
        $(
            impl ScalarLength for $x {
                type Elem = u8;
                fn n_elems(&self) -> usize {
                    self.len()
                }
            }
        )+
    }
}

impl_scalar_len!(T; [T], &'_ [T], Vec<T>);
impl_scalar_len! { str, &'_ str, std::borrow::Cow<'_, str>, String }