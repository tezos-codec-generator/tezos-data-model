use criterion::{black_box, criterion_group, criterion_main, Criterion};

use tedium::{SliceParser, TryIntoParser, ByteParser, MemoParser};


const INPUT: &'static [u8] = b"This is a sample buffer we wish to parse out and figure out which is faster, ByteParser or SliceParser.";

fn byte_bench(c: &mut Criterion) {
    c.bench_function("byteparser_iterate", |b| {
        b.iter(|| black_box(for _ in TryIntoParser::<ByteParser>::try_into_parser(INPUT).unwrap() {}))
    });
}

fn memo_bench(c: &mut Criterion) {
    c.bench_function("memoparser_iterate", |b| {
        b.iter(|| black_box(for _ in TryIntoParser::<MemoParser>::try_into_parser(INPUT).unwrap() {}))
    });
}

fn slice_bench(c: &mut Criterion) {
    c.bench_function("sliceparser_iterate", |b| {
        b.iter(|| black_box(for _ in TryIntoParser::<SliceParser>::try_into_parser(INPUT).unwrap() {}))
    });
}

criterion_group! {
    name = parser_benches;
    config = Criterion::default();
    targets = byte_bench, slice_bench, memo_bench
}

criterion_main!(parser_benches);
