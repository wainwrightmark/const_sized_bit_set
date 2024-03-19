# Const Sized Bit Set

![GITHUB](https://img.shields.io/github/last-commit/wainwrightmark/const_sized_bit_set)

A bitset with a const generic size parameter indicating the number of 64 bit words to use.
Can be used in no-std as it does not allocate.

## Getting started

```rust
use const_sized_bit_set::*;

// This set has 2 64-bit words so this set can contain values in 0..=127
let mut set = BitSet::<2>::from_iter([0,1, 99].into_iter());

set.remove(1);
set.insert(100);

assert_eq!(set.to_string(), "[0, 99, 100]");

```
