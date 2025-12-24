#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![deny(warnings, dead_code, unused_imports, unused_mut)]
#![warn(clippy::pedantic)]
#![allow(clippy::double_must_use)]
pub mod bit_map;
pub mod bit_set_array;
pub mod bit_set_n;
pub mod bit_set_trait;
#[cfg(any(test, feature = "std"))]
pub mod bit_set_vec;
pub mod finite;
pub mod iterator;
pub mod set_size_n_iter;
pub mod shiftable;
pub mod subset_iter;
pub mod n_choose_k;
pub mod slice_iter;

pub type SetElement = u32;

use crate::bit_set_array::BitSetArray;
use crate::bit_set_n::{BitSet8, BitSet16, BitSet32, BitSet64, BitSet128};

pub mod prelude {
    pub use crate::bit_set_array::BitSetArray;
    pub use crate::bit_set_n::*;
    pub use crate::bit_set_trait::BitSet;
    #[cfg(any(test, feature = "std"))]
    pub use crate::bit_set_vec::BitSetVec;
    pub use crate::finite::FiniteBitSet;
    pub use crate::shiftable::ShiftableBitSet;
}
