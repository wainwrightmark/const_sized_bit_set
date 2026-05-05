use crate::prelude::*;

/// Allows you to get the first N elements of a set as a constant.
pub trait FirstNBitSet<const N: usize>: crate::prelude::BitSet {
    /// The fist N elements of the set
    const FIRST_N: Self;
}

macro_rules! impl_first_n_bitset {
    ($name:ident) => {
        impl<const N: usize> FirstNBitSet<N> for $name {
            const FIRST_N: Self = Self::from_first_n_const(N as u32);
        }
    };
}

impl_first_n_bitset!(BitSet8);
impl_first_n_bitset!(BitSet16);
impl_first_n_bitset!(BitSet32);
impl_first_n_bitset!(BitSet64);
impl_first_n_bitset!(BitSet128);

impl<const WORDS: usize, const N: usize> FirstNBitSet<N> for BitSetArray<WORDS> {
    const FIRST_N: Self = Self::from_first_n_const(N as u32);
}


#[cfg(test)]
mod tests{
    use crate::prelude::{BitSet, BitSet8, FirstNBitSet};
  
    #[test]
    fn test_first_n(){
        const FN: BitSet8 = <BitSet8 as FirstNBitSet<7>>::FIRST_N;

        assert_eq!(FN.into_inner(), 0b01111111);
    }
}