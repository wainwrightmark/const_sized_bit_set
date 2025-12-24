# Const Sized Bit Set

![GITHUB](https://img.shields.io/github/last-commit/wainwrightmark/const_sized_bit_set)

This crate is intended to provide every bitset and every function of bitsets that you will ever need.

It is no-std compatible (apart from the `BitVec` type), uses no unsafe code, and has no dependencies (except behind the `serde` feature).

Most functions are available both on traits to allow you to use these sets in generic contexts, and as const functions (with '_const' suffix) so you can use them in const functions.

I've optimized for general performance across a variety of situations. There are several areas (particularly iterators) where I've improved performance a lot over a naive implementation. But obviously performance is mercurial, subjective, and platform dependent. Get in touch if you need maximum performance for a specific use case as I may have suggestions.

## Getting started

```rust
use const_sized_bit_set::*;

// This set has 2 64-bit words so this set can contain values in 0..=127
let mut set = BitSetArray::<2>::from_iter([0,1, 99].into_iter());

set.remove(1);
set.insert(100);

assert_eq!(set.to_string(), "[0, 99, 100]");

```

## BitSets

| Name          | Maximum Number Of Elements                             | Required Feature |
|---------------|--------------------------------------------------------|------------------|
| `BitSet8`     | 8                                                      |                  |
| `BitSet16`    | 16                                                     |                  |
| `BitSet32`    | 32                                                     |                  |
| `BitSet64`    | 64                                                     |                  |
| `BitSet128`   | 128                                                    |                  |
| `BitSetArray` | Any multiple of 64, chosen statically at compile time. |                  |
| `BitSetVec`   | Any, but requires allocation                           | `std`            |

All of the above sets implement `BitSet`.
All of the above sets apart from `BitSetVec` implement `FiniteBitSet`

## Subsets

The method `iter_subsets` is provided for iterating through subsets of a given size.
For example the size 2 subsets of the set [1,4,7] are, in order, [1,4], [1,7], and [4,7].
There are also methods available to get a subset by index and to get the index of a particular subset.  



