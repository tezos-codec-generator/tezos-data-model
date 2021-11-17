use std::str::FromStr;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use num_bigint::{BigInt, BigUint};
use rug::Integer;

use rust_runtime::Zarith;

fn rug_bench(c: &mut Criterion) {
    use rust_runtime::zarith::n::nat_rug::N;
    use rust_runtime::zarith::z::int_rug::Z;
    let n = N(Integer::from_str("127461384761974461239474173621436").unwrap());
    let z = Z(Integer::from_str("-127461384761974461239474173621436").unwrap());

    let n_bytes = &n.serialize();
    let z_bytes = &z.serialize();

    c.bench_function("nat_rug_to", |b| b.iter(|| black_box(n.serialize())));
    c.bench_function("nat_rug_from", |b| b.iter(|| black_box(N::deserialize(n_bytes))));
    c.bench_function("int_rug_to", |b| b.iter(|| black_box(z.serialize())));
    c.bench_function("int_rug_from", |b| b.iter(|| black_box(Z::deserialize(z_bytes))));
}

fn big_bench(c: &mut Criterion) {
    use rust_runtime::zarith::n::nat_big::N;
    use rust_runtime::zarith::z::int_big::Z;

    let n = N(BigUint::from_str("127461384761974461239474173621436").unwrap());
    let z = Z(BigInt::from_str("-127461384761974461239474173621436").unwrap());

    let n_bytes = &n.serialize();
    let z_bytes = &z.serialize();

    c.bench_function("nat_big_to", |b| b.iter(|| black_box(n.serialize())));
    c.bench_function("nat_big_from", |b| b.iter(|| black_box(N::deserialize(n_bytes))));
    c.bench_function("int_big_to", |b| b.iter(|| black_box(z.serialize())));
    c.bench_function("int_big_from", |b| b.iter(|| black_box(Z::deserialize(z_bytes))));
}

criterion_group!(benches, rug_bench, big_bench);
criterion_main!(benches);