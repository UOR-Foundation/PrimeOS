use criterion::{black_box, criterion_group, criterion_main, Criterion};
use primeos_codec::{encode, decode};

fn benchmark_encode(c: &mut Criterion) {
    let small_data = vec![42u8; 32];
    let medium_data = vec![42u8; 1024];
    let large_data = vec![42u8; 8192];

    c.bench_function("encode_32_bytes", |b| {
        b.iter(|| encode(black_box(&small_data)))
    });

    c.bench_function("encode_1kb", |b| {
        b.iter(|| encode(black_box(&medium_data)))
    });

    c.bench_function("encode_8kb", |b| {
        b.iter(|| encode(black_box(&large_data)))
    });
}

fn benchmark_decode(c: &mut Criterion) {
    let small_data = vec![42u8; 32];
    let medium_data = vec![42u8; 1024];
    let large_data = vec![42u8; 8192];

    let small_digest = encode(&small_data).unwrap();
    let medium_digest = encode(&medium_data).unwrap();
    let large_digest = encode(&large_data).unwrap();

    c.bench_function("decode_32_bytes", |b| {
        b.iter(|| decode(black_box(&small_digest)))
    });

    c.bench_function("decode_1kb", |b| {
        b.iter(|| decode(black_box(&medium_digest)))
    });

    c.bench_function("decode_8kb", |b| {
        b.iter(|| decode(black_box(&large_digest)))
    });
}

fn benchmark_round_trip(c: &mut Criterion) {
    let data = vec![42u8; 256];

    c.bench_function("round_trip_256_bytes", |b| {
        b.iter(|| {
            let digest = encode(black_box(&data)).unwrap();
            decode(black_box(&digest))
        })
    });
}

criterion_group!(benches, benchmark_encode, benchmark_decode, benchmark_round_trip);
criterion_main!(benches);