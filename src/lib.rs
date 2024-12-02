#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![deny(warnings, dead_code, unused_imports, unused_mut)]
#![warn(clippy::pedantic)]
#![allow(clippy::double_must_use)]
pub mod bit_set_array;
pub mod bit_set_iterator;
pub mod bit_set_n;
pub mod bit_set_shiftable;
pub mod bit_set_trait;
mod n_choose_k;
pub mod set_size_n_iter;

pub type SetElement = u32;
pub use bit_set_array::*;
pub use bit_set_n::*;
