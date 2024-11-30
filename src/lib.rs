#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![deny(warnings, dead_code, unused_imports, unused_mut)]
#![warn(clippy::pedantic)]
#![allow(clippy::double_must_use)]
mod n_choose_k;
pub mod bit_set;
pub mod bit_set_n;

pub use bit_set::*;
pub use bit_set_n::*;