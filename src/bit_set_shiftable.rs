use crate::{
    bit_set_trait::BitSetTrait, BitSet128, BitSet16, BitSet32, BitSet64, BitSet8, SetElement,
};

pub trait BitSetShiftable: BitSetTrait {
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
        impl BitSetShiftable for $name {
            fn t_zeros(&self) -> u32 {
                self.inner().trailing_zeros()
            }

            fn t_ones(&self) -> u32 {
                self.inner().trailing_ones()
            }

            fn l_zeros(&self) -> u32 {
                self.inner().leading_zeros()
            }

            fn l_ones(&self) -> u32 {
                self.inner().leading_ones()
            }

            fn shift_right(&mut self, n: SetElement) {
                *self = Self::from_inner(self.inner() >> n)
            }

            fn shift_left(&mut self, n: SetElement) {
                *self = Self::from_inner(self.inner() << n)
            }
        }
    };
}

impl_bit_set_shiftable!(BitSet8);
impl_bit_set_shiftable!(BitSet16);
impl_bit_set_shiftable!(BitSet32);
impl_bit_set_shiftable!(BitSet64);
impl_bit_set_shiftable!(BitSet128);
