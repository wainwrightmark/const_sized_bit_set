use const_sized_bit_set::*;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Sum_all");

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 1));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| sum_elements::<1>(black_box(BitSet::ALL)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 2));
    group.bench_with_input(BenchmarkId::from_parameter(2), &(), |b, &()| {
        b.iter(|| sum_elements::<2>(black_box(BitSet::ALL)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 3));
    group.bench_with_input(BenchmarkId::from_parameter(3), &(), |b, &()| {
        b.iter(|| sum_elements::<3>(black_box(BitSet::ALL)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 4));
    group.bench_with_input(BenchmarkId::from_parameter(4), &(), |b, &()| {
        b.iter(|| sum_elements::<4>(black_box(BitSet::ALL)));
    });

    group.finish();


    let mut group = c.benchmark_group("Sum_with_fold_all");

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 1));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements::<1>(black_box(BitSet::ALL)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 2));
    group.bench_with_input(BenchmarkId::from_parameter(2), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements::<2>(black_box(BitSet::ALL)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 3));
    group.bench_with_input(BenchmarkId::from_parameter(3), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements::<3>(black_box(BitSet::ALL)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 4));
    group.bench_with_input(BenchmarkId::from_parameter(4), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements::<4>(black_box(BitSet::ALL)));
    });

    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

fn sum_elements<const W: usize>(set: BitSet<W>) -> usize {
    let mut sum = 0usize;
    for x in set.into_iter() {
        sum = sum.wrapping_add(x);
    }
    sum
}

fn sum_with_fold_elements<const W: usize>(set: BitSet<W>) -> usize {
    set.into_iter().fold(0, |acc,x|acc + x)
}
