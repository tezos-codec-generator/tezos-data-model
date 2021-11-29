use criterion::{criterion_group, criterion_main, Criterion};

use rust_runtime::{Builder, LazyBuilder, OwnedBuilder, StrictBuilder};

const TEXT: [&'static str; 5] = [
    "There once was a novice rustacean",
    "who attempted delayed computation",
    "by splitting in chunks",
    "and enqueueing thunks",
    "with an ultimate finalization",
];

fn lazy_bench(c: &mut Criterion) {
    fn run(n: usize) -> Vec<u8> {
        let mut bld = LazyBuilder::empty();

        for _ in 0..n {
            bld += LazyBuilder::from(TEXT[0].as_bytes());
            bld += LazyBuilder::from(TEXT[1].as_bytes());
            bld += LazyBuilder::from(TEXT[2].as_bytes());
            bld += LazyBuilder::from(TEXT[3].as_bytes());
            bld += LazyBuilder::from(TEXT[4].as_bytes());
        }

        bld.into_vec()
    }

    c.bench_function("lazy_accum", |b| b.iter(|| run(100)));
}

fn strict_bench(c: &mut Criterion) {
    fn run(n: usize) -> Vec<u8> {
        let mut bld = StrictBuilder::empty();

        for _ in 0..n {
            bld += StrictBuilder::from(TEXT[0].as_bytes());
            bld += StrictBuilder::from(TEXT[1].as_bytes());
            bld += StrictBuilder::from(TEXT[2].as_bytes());
            bld += StrictBuilder::from(TEXT[3].as_bytes());
            bld += StrictBuilder::from(TEXT[4].as_bytes());
        }

        bld.into_vec()
    }

    c.bench_function("strict_accum", |b| b.iter(|| run(100)));
}

fn owned_bench(c: &mut Criterion) {
    fn run(n: usize) -> Vec<u8> {
        let mut bld = OwnedBuilder::empty();

        for _ in 0..n {
            bld += TEXT[0].as_bytes();
            bld += TEXT[1].as_bytes();
            bld += TEXT[2].as_bytes();
            bld += TEXT[3].as_bytes();
            bld += TEXT[4].as_bytes();
        }

        bld.into_vec()
    }

    c.bench_function("owned_accum", |b| b.iter(|| run(100)));
}

criterion_group! {
    name = builder_benches;
    config = Criterion::default();
    targets = lazy_bench, owned_bench, strict_bench
}

criterion_main!(builder_benches);
