use crate::{BitSet8, BitSet16, BitSet32, BitSet64, BitSet128, SetElement, bit_set_trait::BitSet};

pub trait ShiftableBitSet: BitSet {
    /// Equivalent to `trailing_zeros`
    fn t_zeros(&self) -> u32;

    /// Equivalent to `trailing_ones`
    fn t_ones(&self) -> u32;

    /// Equivalent to `leading_zeros`
    fn l_zeros(&self) -> u32;

    /// Equivalent to `leading_ones`
    fn l_ones(&self) -> u32;

    /// Equivalent to >>=
    /// Reduce the value of every element in the set by n, removing elements that are no longer in range
    fn shift_right(&mut self, n: SetElement);

    /// Equivalent to <<=
    /// Increase the value of every element in the set by n, removing elements that are no longer in range
    fn shift_left(&mut self, n: SetElement);
}

macro_rules! impl_bit_set_shiftable {
    ($name:ident) => {
        impl ShiftableBitSet for $name {
            fn t_zeros(&self) -> u32 {
                self.into_inner_const().trailing_zeros()
            }

            fn t_ones(&self) -> u32 {
                self.into_inner_const().trailing_ones()
            }

            fn l_zeros(&self) -> u32 {
                self.into_inner_const().leading_zeros()
            }

            fn l_ones(&self) -> u32 {
                self.into_inner_const().leading_ones()
            }

            fn shift_right(&mut self, n: SetElement) {
                *self = Self::from_inner(self.into_inner_const() >> n)
            }

            fn shift_left(&mut self, n: SetElement) {
                *self = Self::from_inner(self.into_inner_const() << n)
            }
        }
    };
}

impl_bit_set_shiftable!(BitSet8);
impl_bit_set_shiftable!(BitSet16);
impl_bit_set_shiftable!(BitSet32);
impl_bit_set_shiftable!(BitSet64);
impl_bit_set_shiftable!(BitSet128);
