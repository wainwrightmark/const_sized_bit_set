use const_sized_bit_set::prelude::*;
use iai_callgrind::{library_benchmark, library_benchmark_group, main};

use std::hint::black_box;

const FULL_SET: BitSetArray<4> = BitSetArray::ALL;
const EMPTY_SET: BitSetArray<4> = BitSetArray::EMPTY;

/// These numbers have been selected randomly, but of course they are the same every time
const RANDOM_SET: BitSetArray<4> = BitSetArray::from_inner_const([
    0b1001000101101011101011011011011010100110101011100001000100100001,
    0b0010101001000010100111111101001110100111101111000111100101010001,
    0b1110100110001111100101101001101001000110010010001111111011001001,
    0b0101010010001111000001000111000110111011111101010011101010111001,
]);
const HALF_EMPTY_SET: BitSetArray<4> = BitSetArray::from_inner_const(
    [0b101010101010101010101010101010101010101010101010101010101010101; 4],
);

#[library_benchmark]
#[bench::full(FULL_SET)]
#[bench::half(HALF_EMPTY_SET)]
#[bench::empty(EMPTY_SET)]
#[bench::random(RANDOM_SET)]
fn sum_all_elements_with_sum(set: BitSetArray<4>) -> u32 {
    black_box(set).into_iter().sum()
}

#[library_benchmark]
#[bench::full(FULL_SET)]
#[bench::half(HALF_EMPTY_SET)]
#[bench::empty(EMPTY_SET)]
#[bench::random(RANDOM_SET)]
fn sum_all_elements_next(set: BitSetArray<4>) -> u32 {
    let mut acc = 0u32;
    let iter = black_box(set).into_iter();
    for x in iter {
        acc = acc.wrapping_add(x);
    }
    acc
}

#[library_benchmark]
#[bench::full(FULL_SET)]
#[bench::half(HALF_EMPTY_SET)]
#[bench::empty(EMPTY_SET)]
#[bench::random(RANDOM_SET)]
fn sum_all_elements_next_back(set: BitSetArray<4>) -> u32 {
    let mut acc = 0u32;
    let mut iter = black_box(set).into_iter();
    while let Some(x) = iter.next_back() {
        acc = acc.wrapping_add(x);
    }
    acc
}

#[library_benchmark]
#[bench::full(FULL_SET)]
#[bench::half(HALF_EMPTY_SET)]
#[bench::empty(EMPTY_SET)]
#[bench::random(RANDOM_SET)]
fn sum_all_elements_fold(set: BitSetArray<4>) -> u32 {
    black_box(set)
        .into_iter()
        .fold(0, |acc, x| acc.wrapping_add(x))
}

#[library_benchmark]
#[bench::full(FULL_SET)]
#[bench::half(HALF_EMPTY_SET)]
#[bench::empty(EMPTY_SET)]
#[bench::random(RANDOM_SET)]
fn sum_all_elements_rfold(set: BitSetArray<4>) -> u32 {
    black_box(set)
        .into_iter()
        .rfold(0, |acc, x| acc.wrapping_add(x))
}

#[library_benchmark]
#[bench::full_100(FULL_SET, 100)]
#[bench::half_100(HALF_EMPTY_SET, 100)]
#[bench::empty_100(EMPTY_SET, 100)]
#[bench::random_100(RANDOM_SET, 100)]
fn nth_forward(set: BitSetArray<4>, n: usize) -> Option<u32> {
    black_box(set).into_iter().nth(black_box(n))
}

#[library_benchmark]
#[bench::all_100(BitSetArray::ALL, 100)]
#[bench::half_100(HALF_EMPTY_SET, 100)]
#[bench::empty_100(EMPTY_SET, 100)]
#[bench::random_100(RANDOM_SET, 100)]
fn nth_back(set: BitSetArray<4>, n: usize) -> Option<u32> {
    black_box(set).into_iter().nth_back(black_box(n))
}

#[library_benchmark]
fn is_subset() -> usize {
    let all = black_box(BitSetArray::<4>::ALL);
    let mut count = 0;
    for index in [63, 127, 191, 255] {
        let set = black_box(BitSetArray::EMPTY.with_inserted(index));

        if set.is_subset_const(&all) {
            count += 1;
        }
    }

    count
}

#[library_benchmark]
fn create_from_fn() -> BitSetArray<4> {
    BitSetArray::from_fn(|x| x % black_box(3) == 0)
}

library_benchmark_group!(
    name = sum_elements;
    benchmarks = sum_all_elements_with_sum, sum_all_elements_next, sum_all_elements_next_back, sum_all_elements_fold, sum_all_elements_rfold
);

library_benchmark_group!(
    name = nth;
    benchmarks = nth_forward, nth_back
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
