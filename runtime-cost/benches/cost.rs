use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use criterion_linux_perf::{PerfMeasurement, PerfMode};

pub fn bash_benchmark(crit: &mut Criterion<PerfMeasurement>) {
    let mut bash_state = [0u8; 192];
    crit.bench_function("bash stub", |b| {
        b.iter(|| runtime_cost::bash_stub(black_box(&mut bash_state)))
    });
    crit.bench_function("bash ref", |b| {
        b.iter(|| runtime_cost::bash(black_box(&mut bash_state)))
    });
    crit.bench_function("bash avx2", |b| {
        b.iter(|| runtime_cost::bash_avx2(black_box(&mut bash_state)))
    });
}

pub fn blake2b_benchmark(crit: &mut Criterion<PerfMeasurement>) {
    let mut group = crit.benchmark_group("blake2b");
    for size in [255u64, 65521u64].iter() {
        group.throughput(Throughput::Bytes(*size));
        group.bench_with_input(BenchmarkId::new("stub", size), size, |b, &size| {
            let data = vec![0u8; size as usize];
            b.iter(|| runtime_cost::blake2b_stub(&mut [0u8; 64], &[0u8; 16], &data));
        });
        group.bench_with_input(BenchmarkId::new("ref", size), size, |b, &size| {
            let data = vec![0u8; size as usize];
            b.iter(|| runtime_cost::blake2b(&mut [0u8; 64], &[0u8; 16], &data));
        });
    }
    group.finish();
}

pub fn chacha20_benchmark(crit: &mut Criterion<PerfMeasurement>) {
    let mut group = crit.benchmark_group("chacha20");
    let key = [0u8; 32];
    let nonce = [0u8; 12];
    for size in [19u64, 255u64, 65521u64].iter() {
        group.throughput(Throughput::Bytes(*size));
        group.bench_with_input(BenchmarkId::new("stub", size), size, |b, &size| {
            let data = vec![0u8; size as usize];
            let mut out = vec![0u8; size as usize];
            b.iter(|| {
                runtime_cost::chacha20_stub(
                    black_box(&mut out),
                    black_box(&key),
                    black_box(0),
                    black_box(&nonce),
                    black_box(&data),
                )
            });
        });
        group.bench_with_input(BenchmarkId::new("ref", size), size, |b, &size| {
            let data = vec![0u8; size as usize];
            let mut out = vec![0u8; size as usize];
            b.iter(|| {
                runtime_cost::chacha20(
                    black_box(&mut out),
                    black_box(&key),
                    black_box(0),
                    black_box(&nonce),
                    black_box(&data),
                )
            });
        });
    }
    group.finish();
}

pub fn gimli_benchmark(crit: &mut Criterion<PerfMeasurement>) {
    let mut gimli_state = [0u8; 48];
    crit.bench_function("gimli stub", |b| {
        b.iter(|| runtime_cost::gimli_stub(black_box(&mut gimli_state)))
    });
    crit.bench_function("gimli ref", |b| {
        b.iter(|| runtime_cost::gimli(black_box(&mut gimli_state)))
    });
    crit.bench_function("gimli avx2", |b| {
        b.iter(|| runtime_cost::gimli_avx2(black_box(&mut gimli_state)))
    });
}

pub fn poly1305_benchmark(crit: &mut Criterion<PerfMeasurement>) {
    let mut group = crit.benchmark_group("poly1305");
    for size in [255u64, 65521u64].iter() {
        group.throughput(Throughput::Bytes(*size));
        group.bench_with_input(BenchmarkId::new("stub", size), size, |b, &size| {
            let plain = vec![0u8; size as usize];
            let mut cipher = vec![0u8; size as usize];
            b.iter(|| runtime_cost::poly1305_stub(&mut cipher, &plain, &[0u8; 32]));
        });
        group.bench_with_input(BenchmarkId::new("ref", size), size, |b, &size| {
            let plain = vec![0u8; size as usize];
            let mut cipher = vec![0u8; size as usize];
            b.iter(|| runtime_cost::poly1305(&mut cipher, &plain, &[0u8; 32]));
        });
        group.bench_with_input(BenchmarkId::new("avx2", size), size, |b, &size| {
            let plain = vec![0u8; size as usize];
            let mut cipher = vec![0u8; size as usize];
            b.iter(|| runtime_cost::poly1305_avx2(&mut cipher, &plain, &[0u8; 32]));
        });
    }
    group.finish();
}

pub fn xxh_benchmark(crit: &mut Criterion<PerfMeasurement>) {
    let mut group = crit.benchmark_group("xxh");
    for size in [19u64, 255u64, 65521u64].iter() {
        group.throughput(Throughput::Bytes(*size));
        group.bench_with_input(BenchmarkId::new("stub", size), size, |b, &size| {
            let data = vec![0u8; size as usize];
            b.iter(|| runtime_cost::xxh_stub(&data, 0));
        });
        group.bench_with_input(BenchmarkId::new("ref", size), size, |b, &size| {
            let data = vec![0u8; size as usize];
            b.iter(|| runtime_cost::xxh(&data, 0));
        });
    }
    group.finish();
}

criterion_group!(
    name = timing;
    config = Criterion::default().sample_size(1000).with_measurement(PerfMeasurement::new(PerfMode::Cycles));
    targets = bash_benchmark, blake2b_benchmark, chacha20_benchmark, gimli_benchmark, poly1305_benchmark, xxh_benchmark
);

criterion_group!(
    name = instruction_count;
    config = Criterion::default().sample_size(20).with_measurement(PerfMeasurement::new(PerfMode::Instructions));
    targets = bash_benchmark, blake2b_benchmark, chacha20_benchmark, gimli_benchmark, poly1305_benchmark, xxh_benchmark
);

criterion_main!(instruction_count, timing);
