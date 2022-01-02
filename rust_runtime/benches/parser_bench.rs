use criterion::{black_box, criterion_group, criterion_main, Criterion};

use rust_runtime::{parse::byteparser::SliceParser, ToParser, ByteParser};

const INPUT: &'static [u8] = b"This is a sample buffer we wish to parse out and figure out which is faster, ByteParser or SliceParser.";

fn byte_bench(c: &mut Criterion) {
    c.bench_function("byteparser_iterate", |b| {
        b.iter(|| black_box(for _ in ToParser::<ByteParser>::to_parser(INPUT) {}))
    });
}

fn slice_bench(c: &mut Criterion) {
    c.bench_function("sliceparser_iterate", |b| {
        b.iter(|| black_box(for _ in ToParser::<SliceParser>::to_parser(INPUT) {}))
    });
}

criterion_group! {
    name = parser_benches;
    config = Criterion::default();
    targets = byte_bench, slice_bench
}

criterion_main!(parser_benches);
