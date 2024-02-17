use const_sized_bit_set::*;
use iai_callgrind::{library_benchmark, library_benchmark_group, main};

use std::hint::black_box;

fn sum_elements<const W: usize>(set: BitSet<W>) -> usize {
    let mut sum = 0usize;
    for x in set.into_iter() {
        sum = sum.wrapping_add(x);
    }
    sum
}

fn sum_elements_fold<const W: usize>(set: BitSet<W>) -> usize {
    set.into_iter().fold(0, |acc, v| acc.wrapping_add(v))
}

fn sum_elements_rfold<const W: usize>(set: BitSet<W>) -> usize {
    set.into_iter().rfold(0, |acc, v| acc.wrapping_add(v))
}

fn sum_elements_back<const W: usize>(set: BitSet<W>) -> usize {
    let mut sum = 0usize;
    for x in set.into_iter().rev() {
        sum = sum.wrapping_add(x);
    }
    sum
}

#[library_benchmark]
fn sum_all_elements_1() -> usize {
    sum_elements::<1>(black_box(BitSet::ALL))
}

#[library_benchmark]
fn sum_all_elements_4() -> usize {
    sum_elements::<4>(black_box(BitSet::ALL))
}

const HALF_EMPTY_SET: BitSet<1> = BitSet::EMPTY
    .with_inserted(0)
    .with_inserted(2)
    .with_inserted(4)
    .with_inserted(6)
    .with_inserted(8)
    .with_inserted(10)
    .with_inserted(12)
    .with_inserted(14)
    .with_inserted(16)
    .with_inserted(18)
    .with_inserted(20)
    .with_inserted(22)
    .with_inserted(24)
    .with_inserted(26)
    .with_inserted(28)
    .with_inserted(30)
    .with_inserted(32)
    .with_inserted(34)
    .with_inserted(36)
    .with_inserted(38)
    .with_inserted(40)
    .with_inserted(42)
    .with_inserted(44)
    .with_inserted(46)
    .with_inserted(48)
    .with_inserted(50)
    .with_inserted(52)
    .with_inserted(54)
    .with_inserted(56)
    .with_inserted(58)
    .with_inserted(60)
    .with_inserted(62);

#[library_benchmark]
fn sum_half_elements() -> usize {
    sum_elements::<1>(black_box(HALF_EMPTY_SET))
}

#[library_benchmark]
fn sum_half_elements_fold() -> usize {
    sum_elements_fold::<1>(black_box(HALF_EMPTY_SET))
}

#[library_benchmark]
fn sum_all_elements_fold_1() -> usize {
    sum_elements_fold::<1>(black_box(BitSet::ALL))
}

#[library_benchmark]
fn sum_all_elements_fold_4() -> usize {
    sum_elements_fold::<4>(black_box(BitSet::ALL))
}

#[library_benchmark]
fn sum_all_elements_back_1() -> usize {
    sum_elements_back::<1>(black_box(BitSet::ALL))
}
#[library_benchmark]
fn sum_all_elements_back_4() -> usize {
    sum_elements_back::<4>(black_box(BitSet::ALL))
}

#[library_benchmark]
fn sum_all_elements_rfold_1() -> usize {
    sum_elements_rfold::<1>(black_box(BitSet::ALL))
}

#[library_benchmark]
fn sum_all_elements_rfold_4() -> usize {
    sum_elements_rfold::<4>(black_box(BitSet::ALL))
}

#[library_benchmark]
fn nth_half_10() -> Option<usize> {
    black_box(HALF_EMPTY_SET).into_iter().nth(black_box(10))
}

#[library_benchmark]
fn nth_all_100() -> Option<usize> {
    black_box(BitSet::<4>::ALL).into_iter().nth(black_box(100))
}

#[library_benchmark]
fn nth_back_half_10() -> Option<usize> {
    black_box(HALF_EMPTY_SET)
        .into_iter()
        .nth_back(black_box(10))
}

#[library_benchmark]
fn nth_back_all_100() -> Option<usize> {
    black_box(BitSet::<4>::ALL)
        .into_iter()
        .nth_back(black_box(100))
}

#[library_benchmark]
fn is_subset() -> usize {
    let all = black_box(BitSet::<4>::ALL);
    let mut count = 0;
    for index in [63, 127, 191, 255] {
        let set = black_box(BitSet::EMPTY.with_inserted(index));

        if set.is_subset(&all) {
            count += 1;
        }
    }

    count
}

#[library_benchmark]
fn create_from_fn() -> BitSet<4> {
    BitSet::from_fn(|x| x % black_box(3) == 0)
}

library_benchmark_group!(
    name = sum_elements;
    benchmarks = sum_all_elements_1, sum_all_elements_4, sum_all_elements_back_1, sum_all_elements_back_4, sum_all_elements_fold_1, sum_all_elements_fold_4, sum_all_elements_rfold_1, sum_all_elements_rfold_4, sum_half_elements, sum_half_elements_fold
);

library_benchmark_group!(
    name = nth;
    benchmarks = nth_half_10, nth_all_100, nth_back_half_10, nth_back_all_100
);

library_benchmark_group!(
    name = subset;
    benchmarks = is_subset
);

library_benchmark_group!(
    name = from_fn;
    benchmarks = create_from_fn
);

main!(
    library_benchmark_groups = sum_elements,
    subset,
    from_fn,
    nth
);
