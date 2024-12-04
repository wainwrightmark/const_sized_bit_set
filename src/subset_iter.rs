use core::num::NonZeroU32;

use crate::{
    bit_set_shiftable::BitSetShiftable, bit_set_trait::BitSetTrait, BitSet128, BitSet16, BitSet32,
    BitSet64, BitSet8,
};

#[derive(Debug, Clone, PartialEq)]
pub struct SubsetIter<T: BitSetTrait + BitSetShiftable, const BITS: usize> {
    next_set: T,
    // Maps each element index to the element index to the left.
    // Maps indexes of missing elements and of the leftmost element to `0`
    mappings: [u8; BITS],
}

impl<T: BitSetTrait + BitSetShiftable, const BITS: usize> SubsetIter<T, BITS> {
    #[allow(clippy::cast_possible_truncation)]
    pub fn new(superset: &T, subset_size: NonZeroU32) -> Self {
        //todo allow zero
        let mut offsets = [0; BITS];
        let mut previous_index = 0u8;
        let mut ss = *superset;
        while let Some(new_last) = ss.pop_last() {
            offsets[new_last as usize] = previous_index;
            previous_index = new_last as u8;
        }

        let next_set = match superset.nth(subset_size.get() - 1) {
            Some(nth_element) => superset.with_intersect(&T::from_first_n(nth_element + 1)),
            None => {
                //not enough elements in the set - return the empty set which will lead to an empty iterator
                T::EMPTY
            }
        };

        Self {
            next_set,
            mappings: offsets,
        }
    }
}

impl<T: BitSetTrait + BitSetShiftable, const BITS: usize> core::iter::FusedIterator
    for SubsetIter<T, BITS>
{
}

impl<T: BitSetTrait + BitSetShiftable, const BITS: usize> Iterator for SubsetIter<T, BITS> {
    type Item = T;

    #[allow(warnings)]
    fn next(&mut self) -> Option<Self::Item> {
        let next_set = self.next_set.clone();

        let Some(left_most_index) = self.next_set.pop_last() else {
            return None;
        };

        let mapped_index = self.mappings[left_most_index as usize];

        if mapped_index != 0 {
            // the fast path - just move the leftmost index one to the left

            self.next_set.insert(mapped_index as u32);
            return Some(next_set);
        }

        let mut previous_index = left_most_index as u8;
        let mut count_to_add_back = 1;

        loop {
            let Some(new_leftmost) = self.next_set.pop_last() else {
                // there is nothing left to move left. We have finished iterating
                return Some(next_set);
            };
            count_to_add_back += 1;

            let new_leftmost_mapped = self.mappings[new_leftmost as usize];

            if new_leftmost_mapped < previous_index {
                let mut index_to_add_back = new_leftmost_mapped as u32;
                for _ in 0..count_to_add_back {
                    self.next_set.insert(index_to_add_back);
                    index_to_add_back = self.mappings[index_to_add_back as usize] as u32;
                }

                return Some(next_set);
            } else {
                previous_index = new_leftmost as u8;
            }
        }

        // Next set being empty indicates we are finished
        if next_set.is_empty() {
            return None;
        }

        return Some(next_set);
    }

    //todo last, min, max
}

macro_rules! impl_iter_subsets {
    ($bit_set: ty, $bits:expr) => {
        impl $bit_set {
            #[must_use]
            pub fn iter_subsets(&self, subset_size: NonZeroU32) -> SubsetIter<Self, $bits> {
                SubsetIter::new(self, subset_size)
            }
        }
    };
}

impl_iter_subsets!(BitSet8, 8);
impl_iter_subsets!(BitSet16, 16);
impl_iter_subsets!(BitSet32, 32);
impl_iter_subsets!(BitSet64, 64);
impl_iter_subsets!(BitSet128, 128);

#[cfg(test)]
mod tests {
    use core::num::NonZeroU32;

    use crate::{bit_set_trait::BitSetTrait, BitSet8};

    #[test]
    pub fn test_subsets_size_8() {
        let superset = BitSet8::ALL;

        assert_eq!(
            superset
                .iter_subsets(NonZeroU32::new(8).unwrap())
                .collect::<Vec<_>>(),
            vec![BitSet8::ALL]
        );
    }

    #[test]
    pub fn test_subsets_size_7() {
        let superset = BitSet8::ALL;

        assert_eq!(
            superset
                .iter_subsets(NonZeroU32::new(7).unwrap())
                .collect::<Vec<_>>(),
            vec![
                BitSet8::from_inner_const(0b01111111),
                BitSet8::from_inner_const(0b10111111),
                BitSet8::from_inner_const(0b11011111),
                BitSet8::from_inner_const(0b11101111),
                BitSet8::from_inner_const(0b11110111),
                BitSet8::from_inner_const(0b11111011),
                BitSet8::from_inner_const(0b11111101),
                BitSet8::from_inner_const(0b11111110),
            ]
        );
    }

    #[test]
    pub fn fuzz_test() {
        fn test_subsets(actual: &[BitSet8], superset: BitSet8, size: u32) {
            let expected_count = crate::n_choose_k::n_choose_k(superset.len_const(), size);

            assert_eq!(
                actual.len() as u32,
                expected_count,
                "Wrong number of subsets"
            );

            for set in actual {
                assert!(
                    set.is_subset_const(&superset),
                    "Set {set:?} is not a subset of {superset:?}"
                );
            }

            let mut sorted = actual.into_iter().copied().collect::<Vec<_>>();
            sorted.sort();

            let _assert_unique = sorted.into_iter().reduce(|prev, x| {
                assert_ne!(prev, x);
                x
            });
        }

        for bitset in 0..=u8::MAX {
            let bitset = BitSet8::from_inner_const(bitset);
            for size in 1..=bitset.len_const() {
                let subsets = bitset
                    .iter_subsets(NonZeroU32::try_from(size).unwrap())
                    .collect::<Vec<_>>();

                test_subsets(&subsets, bitset, size);
            }
        }
    }

    #[test]
    pub fn test_subsets_size_3() {
        let superset = BitSet8::from_inner(0b11011111);

        assert_eq!(
            superset
                .iter_subsets(NonZeroU32::new(3).unwrap())
                .collect::<Vec<_>>(),
            vec![
                //Note this is 35 lines
                BitSet8::from_inner_const(0b111),
                BitSet8::from_inner_const(0b1011),
                BitSet8::from_inner_const(0b10011),
                BitSet8::from_inner_const(0b1000011),
                BitSet8::from_inner_const(0b10000011),
                BitSet8::from_inner_const(0b1101),
                BitSet8::from_inner_const(0b10101),
                BitSet8::from_inner_const(0b1000101),
                BitSet8::from_inner_const(0b10000101),
                BitSet8::from_inner_const(0b11001),
                BitSet8::from_inner_const(0b1001001),
                BitSet8::from_inner_const(0b10001001),
                BitSet8::from_inner_const(0b1010001),
                BitSet8::from_inner_const(0b10010001),
                BitSet8::from_inner_const(0b11000001),
                BitSet8::from_inner_const(0b1110),
                BitSet8::from_inner_const(0b10110),
                BitSet8::from_inner_const(0b1000110),
                BitSet8::from_inner_const(0b10000110),
                BitSet8::from_inner_const(0b11010),
                BitSet8::from_inner_const(0b1001010),
                BitSet8::from_inner_const(0b10001010),
                BitSet8::from_inner_const(0b1010010),
                BitSet8::from_inner_const(0b10010010),
                BitSet8::from_inner_const(0b11000010),
                BitSet8::from_inner_const(0b11100),
                BitSet8::from_inner_const(0b1001100),
                BitSet8::from_inner_const(0b10001100),
                BitSet8::from_inner_const(0b1010100),
                BitSet8::from_inner_const(0b10010100),
                BitSet8::from_inner_const(0b11000100),
                BitSet8::from_inner_const(0b1011000),
                BitSet8::from_inner_const(0b10011000),
                BitSet8::from_inner_const(0b11001000),
                BitSet8::from_inner_const(0b11010000)
            ]
        );
    }

    #[test]
    pub fn test_subsets_size_2() {
        let superset = BitSet8::from_inner(0b01010101);

        assert_eq!(
            superset
                .iter_subsets(NonZeroU32::new(2).unwrap())
                .collect::<Vec<_>>(),
            vec![
                BitSet8::from_inner_const(0b00000101),
                BitSet8::from_inner_const(0b00010001),
                BitSet8::from_inner_const(0b01000001),
                BitSet8::from_inner_const(0b00010100),
                BitSet8::from_inner_const(0b01000100),
                BitSet8::from_inner_const(0b01010000),
            ]
        );
    }

    #[test]
    pub fn test_subsets_size_1() {
        let superset = BitSet8::from_inner(0b01010101);

        assert_eq!(
            superset
                .iter_subsets(NonZeroU32::new(1).unwrap())
                .collect::<Vec<_>>(),
            vec![
                BitSet8::from_inner_const(0b00000001),
                BitSet8::from_inner_const(0b00000100),
                BitSet8::from_inner_const(0b00010000),
                BitSet8::from_inner_const(0b01000000),
            ]
        );
    }
}
