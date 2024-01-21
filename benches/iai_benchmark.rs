use const_sized_bit_set::*;
use iai::*;

fn sum_elements<const W: usize>(set: BitSet<W>) -> usize {
    let mut sum = 0usize;
    for x in set.into_iter() {
        sum = sum.wrapping_add(x);
    }
    sum
}

fn sum_all_elements_1() -> usize {
    sum_elements::<1>(black_box(BitSet::ALL))
}
fn sum_all_elements_2() -> usize {
    sum_elements::<2>(black_box(BitSet::ALL))
}
fn sum_all_elements_3() -> usize {
    sum_elements::<3>(black_box(BitSet::ALL))
}
fn sum_all_elements_4() -> usize {
    sum_elements::<4>(black_box(BitSet::ALL))
}

iai::main!(sum_all_elements_1, sum_all_elements_2, sum_all_elements_3, sum_all_elements_4);
