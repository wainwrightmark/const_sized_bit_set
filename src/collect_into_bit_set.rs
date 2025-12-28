use crate::prelude::*;

pub trait CollectIntoBitSet<T: BitSet>{
    ///Extend the `set` with all elements from self.
    fn collect_into_bit_set(self, set: &mut T);
}