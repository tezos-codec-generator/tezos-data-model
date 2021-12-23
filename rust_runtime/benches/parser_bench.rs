use criterion::{criterion_group, criterion_main, Criterion, black_box};

use rust_runtime::{Parser, ToParser, parse::byteparser::SliceParser, ByteParser};

const INPUT: &'static [u8] = b"This is a sample buffer we wish to parse out and figure out which is faster, ByteParser or SliceParser.";

fn byte_bench(c: &mut Criterion) {
    c.bench_function("byteparser_iterate", |b| b.iter(|| black_box({
        let mut buf = Vec::<u8>::new();
        for i in INPUT.to_parser() {
            buf.push(i);
        }
    })));
}

fn slice_bench(c: &mut Criterion) {
    c.bench_function("sliceparser_iterate", |b| b.iter(|| black_box({
        let mut buf = Vec::<u8>::new();
        for i in INPUT.to_parser() {
            buf.push(i);
        }
    })));
}

criterion_group! {
    name = parser_benches;
    config = Criterion::default();
    targets = byte_bench, slice_bench
}

criterion_main!(parser_benches);
