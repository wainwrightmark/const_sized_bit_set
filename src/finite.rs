use crate::{BitSet8, BitSet16, BitSet32, BitSet64, BitSet128, SetElement, bit_set_trait::BitSet};

//A Bitset with a finite capacity
pub trait FiniteBitSet: BitSet {
    /// The set of all possible elements
    const ALL: Self;
    /// The total number of elements that can fit in this set
    const CAPACITY: u32;

    /// Negate the elements in the set
    fn negate(&mut self);

    #[must_use]
    fn with_negated(&self) -> Self
    where
        Self: Clone,
    {
        let mut s = self.clone();
        s.negate();
        s
    }

    /// Reverse the elements of the set
    fn reverse(&mut self);

    #[must_use]
    fn with_reversed(&self) -> Self
    where
        Self: Clone,
    {
        let mut s = self.clone();
        s.reverse();
        s
    }

    fn from_fn<F: FnMut(SetElement) -> bool>(mut f: F) -> Self {
        let mut result = Self::EMPTY;
        for x in (0..(Self::CAPACITY)).filter(|x| f(*x)) {
            result.insert(x);
        }

        result
    }

    fn is_all(&self) -> bool;

    fn trailing_zeros(&self) -> u32;
    fn leading_zeros(&self) -> u32;
    fn leading_ones(&self) -> u32;
}

macro_rules! impl_bit_set_finite {
    ($name:ident) => {
        impl FiniteBitSet for $name {
            const ALL: Self = Self::ALL;
            const CAPACITY: u32 = Self::CAPACITY;

            fn negate(&mut self) {
                self.negate_const();
            }

            fn reverse(&mut self) {
                self.reverse_const();
            }

            fn is_all(&self) -> bool {
                self.is_all_const()
            }

            fn trailing_zeros(&self) -> u32 {
                self.into_inner_const().trailing_zeros()
            }

            fn leading_zeros(&self) -> u32 {
                self.into_inner_const().leading_zeros()
            }

            fn leading_ones(&self) -> u32 {
                self.into_inner_const().leading_ones()
            }
        }
    };
}

impl_bit_set_finite!(BitSet8);
impl_bit_set_finite!(BitSet16);
impl_bit_set_finite!(BitSet32);
impl_bit_set_finite!(BitSet64);
impl_bit_set_finite!(BitSet128);
