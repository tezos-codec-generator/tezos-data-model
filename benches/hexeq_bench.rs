use criterion::{black_box, criterion_group, criterion_main, Criterion};

use tedium::HexString;

const INPUT: [u8; 36] = [
    0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf, 0xba, 0xbb, 0xbc, 0xbd, 0xbe, 0xbf, 0xca, 0xcb, 0xcc, 0xcd,
    0xce, 0xcf, 0xda, 0xdb, 0xdc, 0xdd, 0xde, 0xdf, 0xea, 0xeb, 0xec, 0xed, 0xee, 0xef, 0xfa, 0xfb,
    0xfc, 0xfd, 0xfe, 0xff,
];

fn hexeq_bench(c: &mut Criterion) {
    let hex = HexString::from_bytes(INPUT);
    let upper: String = hex.to_hex().to_ascii_uppercase();
    c.bench_function("hexeq_bench", move |b| {
        b.iter(|| black_box(hex.eq_hex(&upper)))
    });
}

criterion_group! {
    name = hexeq_benches;
    config = Criterion::default();
    targets = hexeq_bench
}

criterion_main!(hexeq_benches);
