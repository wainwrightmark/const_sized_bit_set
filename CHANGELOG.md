# Changelog

This project follows semantic versioning.

Possible header types:

- `Features` for any new features added, or for backwards-compatible
  changes to existing functionality.
- `Bug Fixes` for any bug fixes.
- `Breaking Changes` for any backwards-incompatible changes.

[crates.io]: https://crates.io/crates/const_sized_bit_set

## v0.2.1 (2024-04-12)

### Features

- Added `iter_subsets()` for `BitSet8` and friends
- impl `Binary` `UpperHex` and `LowerHex` for `BitSet8` and friends

## v0.2.0

### Breaking Changes

- `BitSet` is renamed `BitSetArray`
- Added `BitSet` trait
- Minimum supported rust version is now 1.83

### Features

- Added `BitSet` trait
- Added `BitSetShiftable` trait
- Added `BitSet8`, `BitSet16`, `BitSet32`, `BitSet64`, `BitSet128`
- Added `SetSizeNIter`

## v0.1.0 (2023-03-19)

- Initial Release on [crates.io] :tada:
