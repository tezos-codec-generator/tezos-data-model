use crate::conv::{Decode, Encode};
use crate::{builder, Parser};

impl Encode for () {
    fn encode<U: builder::Builder>(&self) -> U {
        U::words([])
    }
}

impl Decode for () {
    fn parse<P: Parser>(_: &mut P) -> Self {
        return ();
    }
}

impl Encode for bool {
    fn encode<U: builder::Builder>(&self) -> U {
        match self {
            &true => U::word(0xff),
            &false => U::word(0x00),
        }
    }
}

impl Decode for bool {
    fn parse<P: Parser>(p: &mut P) -> Self {
        p.get_bool().unwrap()
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    #[test]
    fn unit_test() {
        assert_eq!((), <()>::decode(""));
    }
}