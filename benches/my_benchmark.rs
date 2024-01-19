use criterion::{black_box, criterion_group, criterion_main, Criterion};
use const_sized_bit_set::*;

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("Sum all", |b| b.iter(|| sum_elements::<4>(black_box(BitSet::ALL))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

fn sum_elements<const W: usize>(set : BitSet<W>)-> usize{
    let mut sum = 0usize;
    for x in set.into_iter(){
        sum = sum.wrapping_add(x);
    }
    sum
}