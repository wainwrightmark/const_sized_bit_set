# Changelog

This project follows semantic versioning.

Possible header types:

- `Features` for any new features added, or for backwards-compatible
  changes to existing functionality.
- `Bug Fixes` for any bug fixes.
- `Breaking Changes` for any backwards-incompatible changes.

[crates.io]: https://crates.io/crates/const_sized_bit_set

## v0.4.0 (2025-12-18)

### Breaking Changes

- `BitSetArray` now implements `BitSetTrait`. Some of it's methods have been renamed and some now accept/return `u32` instead of `usize`
- Minimum supported rust version is now 1.85 (for 2024 edition)

### Features
- Added `BitMap64`
- impl `BitSetShiftable` for `BitSetArray`
- Added `first_after` and `first_before`

## v0.3.0 (2024-04-12)

### Breaking Changes

- Added `count_lesser_elements` and `nth` to `BitSetTrait`

### Features

- Added `iter_subsets()` for `BitSet8` and friends
- impl `Binary` `UpperHex` and `LowerHex` for `BitSet8` and friends

## v0.2.0

### Breaking Changes

- `BitSet` is renamed `BitSetArray`
- Minimum supported rust version is now 1.83

### Features

- Added `BitSet` trait
- Added `BitSetShiftable` trait
- Added `BitSet8`, `BitSet16`, `BitSet32`, `BitSet64`, `BitSet128`
- Added `SetSizeNIter`

## v0.1.0 (2023-03-19)

- Initial Release on [crates.io] :tada:
