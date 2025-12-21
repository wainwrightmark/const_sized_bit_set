#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![deny(warnings, dead_code, unused_imports, unused_mut)]
#![warn(clippy::pedantic)]
#![allow(clippy::double_must_use)]
pub mod bit_map;
pub mod bit_set_array;
pub mod bit_set_n;
pub mod bit_set_trait;
pub mod finite;
pub mod iterator;
pub mod set_size_n_iter;
pub mod shiftable;
pub mod subset_iter;
#[cfg(any(test, feature = "std"))]
pub mod bit_set_vec;

pub type SetElement = u32;

use crate::bit_set_array::BitSetArray;
use crate::bit_set_n::{BitSet128, BitSet16, BitSet32, BitSet64, BitSet8};

pub mod prelude {    
    pub use crate::bit_set_n::*;
    pub use crate::bit_set_trait::BitSet;
    pub use crate::finite::FiniteBitSet;
    pub use crate::shiftable::ShiftableBitSet;
    pub use crate::bit_set_array::BitSetArray;
    #[cfg(any(test, feature = "std"))]
    pub use crate::bit_set_vec::BitSetVec;
}
