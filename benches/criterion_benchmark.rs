use const_sized_bit_set::*;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

pub fn from_fn_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("from_fn");

    fn create_from_fn<const W: usize>(modulo: usize) -> BitSet<W> {
        BitSet::<W>::from_fn(|x| x % modulo == 0)
    }

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 1));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| create_from_fn::<1>(black_box(2)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 4));
    group.bench_with_input(BenchmarkId::from_parameter(4), &(), |b, &()| {
        b.iter(|| create_from_fn::<4>(black_box(2)));
    });

    group.finish();
}

pub fn sum_all_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Sum_all");

    fn sum_elements<const W: usize>(set: BitSet<W>) -> usize {
        let mut sum = 0usize;
        for x in set.into_iter() {
            sum = sum.wrapping_add(x);
        }
        sum
    }

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 1));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| sum_elements::<1>(black_box(BitSet::ALL)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 4));
    group.bench_with_input(BenchmarkId::from_parameter(4), &(), |b, &()| {
        b.iter(|| sum_elements::<4>(black_box(BitSet::ALL)));
    });

    group.finish();
}

pub fn sum_all_back_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Sum_all_back");

    fn sum_elements_back<const W: usize>(set: BitSet<W>) -> usize {
        let mut sum = 0usize;
        for x in set.into_iter().rev() {
            sum = sum.wrapping_add(x);
        }
        sum
    }

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 1));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| sum_elements_back::<1>(black_box(BitSet::ALL)));
    });

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 4));
    group.bench_with_input(BenchmarkId::from_parameter(4), &(), |b, &()| {
        b.iter(|| sum_elements_back::<4>(black_box(BitSet::ALL)));
    });

    group.finish();
}

pub fn sum_with_fold_all_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Sum_with_fold_all");

    fn sum_with_fold_elements<const W: usize>(set: BitSet<W>) -> usize {
        set.into_iter().fold(0, |acc, x| acc + x)
    }

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 1));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements::<1>(black_box(BitSet::ALL)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 4));
    group.bench_with_input(BenchmarkId::from_parameter(4), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements::<4>(black_box(BitSet::ALL)));
    });

    group.finish();
}

pub fn sum_with_fold_all_back_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Sum_with_fold_all_back");

    fn sum_with_fold_elements_back<const W: usize>(set: BitSet<W>) -> usize {
        set.into_iter().rfold(0, |acc, x| acc + x)
    }

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 1));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements_back::<1>(black_box(BitSet::ALL)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 4));
    group.bench_with_input(BenchmarkId::from_parameter(4), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements_back::<4>(black_box(BitSet::ALL)));
    });

    group.finish();
}

criterion_group!(
    benches,
    from_fn_benchmark,
    sum_all_back_benchmark,
    sum_with_fold_all_back_benchmark,
    sum_all_benchmark,
    sum_with_fold_all_benchmark,
);
criterion_main!(benches);
