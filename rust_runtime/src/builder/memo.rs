#[allow(unused_imports)]
use super::{Builder, TransientBuilder};

#[allow(dead_code)]
pub union Metadata<'a> {
    field_name: &'a str,
    tuple_pos: usize,
}

#[allow(dead_code)]
pub struct Hint<'a> {
    width: usize,
    extra: Metadata<'a>
}

