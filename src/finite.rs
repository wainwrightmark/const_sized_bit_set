use crate::{
    BitSet8, BitSet16, BitSet32, BitSet64, BitSet128, BitSetArray, SetElement,
    bit_set_trait::BitSet,
};

//A Bitset with a finite capacity
pub trait FiniteBitSet: BitSet {
    /// The set of all possible elements
    const ALL: Self;
    /// The total number of elements that can fit in this set
    const CAPACITY: u32;

    fn negate(&mut self);

    #[must_use]
    fn with_negated(&self) -> Self {
        let mut s = self.clone();
        s.negate();
        s
    }

    fn from_fn<F: FnMut(SetElement) -> bool>(mut f: F) -> Self {
        let mut result = Self::EMPTY;
        for x in (0..(Self::CAPACITY)).filter(|x| f(*x)) {
            result.insert(x);
        }

        result
    }
}

macro_rules! impl_bit_set_finite {
    ($name:ident) => {
        impl FiniteBitSet for $name {
            const ALL: Self = Self::ALL;
            const CAPACITY: u32 = Self::CAPACITY;

            fn negate(&mut self) {
                self.negate_const();
            }
        }
    };
}

impl_bit_set_finite!(BitSet8);
impl_bit_set_finite!(BitSet16);
impl_bit_set_finite!(BitSet32);
impl_bit_set_finite!(BitSet64);
impl_bit_set_finite!(BitSet128);

impl<const WORDS: usize> FiniteBitSet for BitSetArray<WORDS> {
    const ALL: Self = Self::ALL;
    const CAPACITY: u32 = Self::CAPACITY;

    fn negate(&mut self) {
        self.negate_const();
    }
}
