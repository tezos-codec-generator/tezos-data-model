use criterion::{black_box, criterion_group, criterion_main, Criterion, Bencher};

static mut IS_SAMPLED : bool = false;
static mut SAMPLE : [u8; 1024] = [1; 1024];

fn init() -> std::io::Result<()> {
    unsafe {
        use std::io::prelude::*;
        let mut f = std::fs::File::open("/dev/urandom").unwrap();
        f.read_exact(&mut SAMPLE).map(|_| { IS_SAMPLED = true; } )
    }
}

fn copy_speed_bench (c: &mut Criterion) {
    let buf : Vec<u8> = unsafe {
        if !IS_SAMPLED {
            init().unwrap();
        }
        SAMPLE.to_vec()
    };

    let mut out1 = std::io::BufWriter::new(std::fs::File::create("/tmp/copy.dump").unwrap());

    c.bench_function("copy", |b| b.iter(|| black_box(std::io::copy(&mut &*buf, &mut out1))));
}

fn write_speed_bench(c: &mut Criterion) {
    let buf : Vec<u8> = unsafe {
        if !IS_SAMPLED {
            init().unwrap();
        }
        SAMPLE.to_vec()
    };

    use std::io::prelude::*;

    let mut out2 = std::io::BufWriter::new(std::fs::File::create("/tmp/write_all.dump").unwrap());

    c.bench_function("write_all", |b: &mut Bencher<_>| b.iter(|| out2.write_all(&mut &*buf)) );
}
criterion_group!(benches, write_speed_bench, copy_speed_bench);
criterion_main!(benches);