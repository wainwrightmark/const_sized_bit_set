use const_sized_bit_set::*;
use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};

pub fn subset_iter_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("subset_iter");

    fn bitset_array_subsets_iter_func(initial_set: BitSetArray<4>, subset_size: u32) -> u32 {
        initial_set
            .iter_subsets(subset_size)
            .map(|x| x.count())
            .sum()
    }

    const INITIAL_BIT_SET_ARRAY: BitSetArray<4> = {
        let mut arr = BitSetArray::EMPTY;
        let mut x = 0u32;
        while x < 256 {
            arr.insert_const(x);
            x += 17;
        }

        arr
    };

    group.bench_with_input(BenchmarkId::from_parameter(5), &5, |b, &subset_size| {
        b.iter(|| bitset_array_subsets_iter_func(INITIAL_BIT_SET_ARRAY, subset_size));
    });

    group.bench_with_input(BenchmarkId::from_parameter(7), &7, |b, &subset_size| {
        b.iter(|| bitset_array_subsets_iter_func(INITIAL_BIT_SET_ARRAY, subset_size));
    });

    const INITIAL_BIT_SET64: BitSet64 = {
        let mut arr = BitSet64::EMPTY;
        let mut x = 0u32;
        while x < 64 {
            arr.insert_const(x);
            x += 7;
        }

        arr
    };

    fn bitset64_subsets_iter_func(initial_set: BitSet64, subset_size: u32) -> u32 {
        initial_set
            .iter_subsets(subset_size)
            .map(|x| x.len_const())
            .sum()
    }

    group.bench_with_input(BenchmarkId::from_parameter("bs64 5"), &5, |b, &subset_size| {
        b.iter(|| bitset64_subsets_iter_func(INITIAL_BIT_SET64, subset_size));
    });
    
    group.bench_with_input(BenchmarkId::from_parameter("bs64 7"), &7, |b, &subset_size| {
        b.iter(|| bitset64_subsets_iter_func(INITIAL_BIT_SET64, subset_size));
    });
}

pub fn from_fn_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("from_fn");

    fn create_from_fn<const W: usize>(modulo: u32) -> BitSetArray<W> {
        BitSetArray::<W>::from_fn(|x| x % modulo == 0)
    }

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| create_from_fn::<1>(black_box(2)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 4));
    group.bench_with_input(BenchmarkId::from_parameter(4), &(), |b, &()| {
        b.iter(|| create_from_fn::<4>(black_box(2)));
    });

    group.finish();
}

pub fn sum_benchmark(c: &mut Criterion) {
    fn sum_elements<const W: usize>(set: BitSetArray<W>) -> u32 {
        let mut sum = 0u32;
        for x in set.into_iter() {
            sum = sum.wrapping_add(x);
        }
        sum
    }

    let mut group = c.benchmark_group("Sum_all");

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| sum_elements::<1>(black_box(BitSetArray::ALL)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 4));
    group.bench_with_input(BenchmarkId::from_parameter(4), &(), |b, &()| {
        b.iter(|| sum_elements::<4>(black_box(BitSetArray::ALL)));
    });

    group.finish();

    let mut group = c.benchmark_group("Sum_half");

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 / 2));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| sum_elements::<1>(black_box(HALF_EMPTY_SET)));
    });

    group.finish();
}

pub fn sum_all_back_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Sum_all_back");

    fn sum_elements_back<const W: usize>(set: BitSetArray<W>) -> u32 {
        let mut sum = 0u32;
        for x in set.into_iter().rev() {
            sum = sum.wrapping_add(x);
        }
        sum
    }

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| sum_elements_back::<1>(black_box(BitSetArray::ALL)));
    });

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 4));
    group.bench_with_input(BenchmarkId::from_parameter(4), &(), |b, &()| {
        b.iter(|| sum_elements_back::<4>(black_box(BitSetArray::ALL)));
    });

    group.finish();
}

pub fn sum_with_fold_benchmark(c: &mut Criterion) {
    fn sum_with_fold_elements<const W: usize>(set: BitSetArray<W>) -> u32 {
        set.into_iter().fold(0, |acc, x| acc + x)
    }

    let mut group = c.benchmark_group("Sum_with_fold_all");

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements::<1>(black_box(BitSetArray::ALL)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 4));
    group.bench_with_input(BenchmarkId::from_parameter(4), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements::<4>(black_box(BitSetArray::ALL)));
    });

    group.finish();

    let mut group = c.benchmark_group("Sum_with_fold_half");

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 / 2));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements::<1>(black_box(HALF_EMPTY_SET)));
    });

    group.finish();
}

pub fn sum_with_fold_all_back_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Sum_with_fold_all_back");

    fn sum_with_fold_elements_back<const W: usize>(set: BitSetArray<W>) -> u32 {
        set.into_iter().rfold(0, |acc, x| acc + x)
    }

    group.throughput(criterion::Throughput::Elements(u64::BITS as u64));
    group.bench_with_input(BenchmarkId::from_parameter(1), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements_back::<1>(black_box(BitSetArray::ALL)));
    });
    group.throughput(criterion::Throughput::Elements(u64::BITS as u64 * 4));
    group.bench_with_input(BenchmarkId::from_parameter(4), &(), |b, &()| {
        b.iter(|| sum_with_fold_elements_back::<4>(black_box(BitSetArray::ALL)));
    });

    group.finish();
}

pub fn nth_benchmark(c: &mut Criterion) {
    c.bench_function("nth_half", |b| {
        b.iter(|| black_box(HALF_EMPTY_SET).into_iter().nth(black_box(10)));
    });

    c.bench_function("nth_all", |b| {
        b.iter(|| {
            black_box(BitSetArray::<4>::ALL)
                .into_iter()
                .nth(black_box(100))
        });
    });

    c.bench_function("nth_back_half", |b| {
        b.iter(|| {
            black_box(HALF_EMPTY_SET)
                .into_iter()
                .nth_back(black_box(10))
        });
    });

    c.bench_function("nth_back_all", |b| {
        b.iter(|| {
            black_box(BitSetArray::<4>::ALL)
                .into_iter()
                .nth_back(black_box(100))
        });
    });
}

criterion_group!(
    benches,
    subset_iter_benchmark,
    sum_with_fold_all_back_benchmark,
    sum_with_fold_benchmark,
    nth_benchmark,
    sum_benchmark,
    from_fn_benchmark,
    sum_all_back_benchmark,
);
criterion_main!(benches);

const HALF_EMPTY_SET: BitSetArray<1> = BitSetArray::from_inner_const([
    0b101010101010101010101010101010101010101010101010101010101010101,
]);
