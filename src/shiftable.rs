use crate::{BitSet8, BitSet16, BitSet32, BitSet64, BitSet128, SetElement, bit_set_trait::BitSet};

pub trait ShiftableBitSet: BitSet {
    /// Equivalent to >>=
    /// Reduce the value of every element in the set by n.
    /// Elements no longer in range are removed.
    fn shift_right(&mut self, n: SetElement);

    /// Equivalent to <<=
    /// For finite sets, elements no longer in range are removed.
    fn shift_left(&mut self, n: SetElement);
}

macro_rules! impl_bit_set_shiftable {
    ($name:ident) => {
        impl ShiftableBitSet for $name {
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
