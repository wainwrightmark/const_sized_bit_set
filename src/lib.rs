#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![deny(warnings, dead_code, unused_imports, unused_mut)]
#![warn(clippy::pedantic)]
#![allow(clippy::double_must_use)]
#![forbid(unsafe_code)]
pub mod bit_set_array;
pub mod bit_set_n;
pub mod bit_set_trait;
#[cfg(any(test, feature = "std"))]
pub mod bit_set_vec;
pub mod finite;
pub mod iterator;
pub mod n_choose_k;
pub mod set_size_n_iter;
pub mod slice_iter;
pub mod subset_iter;
pub mod collect_into_bit_set;

pub type SetElement = u32;

pub mod prelude {
    pub use crate::bit_set_array::BitSetArray;
    pub use crate::bit_set_n::*;
    pub use crate::bit_set_trait::BitSet;
    #[cfg(any(test, feature = "std"))]
    pub use crate::bit_set_vec::BitSetVec;
    pub use crate::finite::FiniteBitSet;
    pub use crate::SetElement;
    pub use crate::collect_into_bit_set::CollectIntoBitSet;
}

#[inline]
pub(crate) fn mutate_inner<R>(inner: &mut u64, f: impl FnOnce(&mut prelude::BitSet64) -> R) -> R {
    let mut set = prelude::BitSet64::from_inner_const(*inner);
    let result = f(&mut set);
    *inner = set.into_inner_const();
    result
}
