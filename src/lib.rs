#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![deny(warnings, dead_code, unused_imports, unused_mut)]
#![warn(clippy::pedantic)]
#![allow(clippy::double_must_use)]
mod n_choose_k;
pub mod bit_set_array;
pub mod bit_set_n;
pub mod bit_set_trait;
pub mod bit_set_shiftable;
pub mod bit_set_iterator;


pub type SetElement = u32;
pub use bit_set_array::*;
pub use bit_set_n::*;

