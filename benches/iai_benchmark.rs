use const_sized_bit_set::*;
use iai_callgrind::{main, library_benchmark_group, library_benchmark};

use std::hint::black_box;

fn sum_elements<const W: usize>(set: BitSet<W>) -> usize {
    let mut sum = 0usize;
    for x in set.into_iter() {
        sum = sum.wrapping_add(x);
    }
    sum
}

#[library_benchmark]
fn sum_all_elements_1() -> usize {
    sum_elements::<1>(black_box(BitSet::ALL))
    
}

#[library_benchmark]
fn sum_all_elements_2() -> usize {
    sum_elements::<2>(black_box(BitSet::ALL))
}

#[library_benchmark]
fn sum_all_elements_3() -> usize {
    sum_elements::<3>(black_box(BitSet::ALL))
}

#[library_benchmark]
fn sum_all_elements_4() -> usize {
    sum_elements::<4>(black_box(BitSet::ALL))
}

#[library_benchmark]
fn is_subset()-> usize{
    let all = black_box(BitSet::<4>::ALL);
    let mut count = 0;
    for index in [63,127,191,255]{
        let set = black_box(BitSet::EMPTY.with_bit_set(index, true));

        if set.is_subset(&all){
            count += 1;
        }
    }

    count
}

library_benchmark_group!(
    name = sum_elements;
    benchmarks = sum_all_elements_1, sum_all_elements_2, sum_all_elements_3, sum_all_elements_4
);

library_benchmark_group!(
    name = subset;
    benchmarks = is_subset
);

main!(library_benchmark_groups = sum_elements, subset);
