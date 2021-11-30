use super::{Builder, TransientBuilder};

pub union Metadata<'a> {
    field_name: &'a str,
    tuple_pos: usize,
}

pub struct Hint<'a> {
    width: usize,
    extra: Metadata<'a>
}

