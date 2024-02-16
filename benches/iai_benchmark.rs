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
    benchmarks = sum_all_elements_1, sum_all_elements_4, sum_all_elements_back_1, sum_all_elements_back_4, sum_all_elements_fold_1, sum_all_elements_fold_4, sum_all_elements_rfold_1, sum_all_elements_rfold_4
);

library_benchmark_group!(
    name = subset;
    benchmarks = is_subset
);

library_benchmark_group!(
    name = from_fn;
    benchmarks = create_from_fn
);

main!(library_benchmark_groups = sum_elements, subset, from_fn);
