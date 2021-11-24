use criterion::{Criterion, criterion_group, criterion_main};

use rust_runtime::{
    conv::{Encode, EncodeLength},
    Builder, LazyBuilder, OwnedBuilder,
};

const TEXT: [&'static str; 5] = [
    "There once was a novice rustacean",
    "who attempted delayed computation",
    "by splitting in chunks",
    "and enqueueing thunks",
    "with an ultimate finalization",
];

fn lazy_bench(c: &mut Criterion) {
    fn run() -> Vec<u8> {
        let mut bld = LazyBuilder::empty();

        bld += TEXT[0].lazy_encode::<LazyBuilder>();
        bld += TEXT[1].lazy_encode::<LazyBuilder>();
        bld += TEXT[2].lazy_encode::<LazyBuilder>();
        bld += TEXT[3].lazy_encode::<LazyBuilder>();
        bld += TEXT[4].lazy_encode::<LazyBuilder>();

        bld.finalize().into_vec()
    }

    c.bench_function("lazy_accum", |b| b.iter(|| run()));
}

fn owned_bench(c: &mut Criterion) {
    fn run() -> Vec<u8> {
        let mut bld = OwnedBuilder::empty();

        bld += TEXT[0].encode::<OwnedBuilder>();
        bld += TEXT[1].encode::<OwnedBuilder>();
        bld += TEXT[2].encode::<OwnedBuilder>();
        bld += TEXT[3].encode::<OwnedBuilder>();
        bld += TEXT[4].encode::<OwnedBuilder>();

        bld.finalize().into_vec()
    }

    c.bench_function("owned_accum", |b| b.iter(|| run()));
}

criterion_group!{
    name = builder_benches;
    config = Criterion::default();
    targets = lazy_bench, owned_bench
}

criterion_main!(builder_benches);
