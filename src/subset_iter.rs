use crate::{BitSet8, BitSet16, BitSet32, BitSet64, BitSet128, bit_set_trait::BitSet};

#[derive(Debug, Clone, PartialEq)]
pub struct SubsetIter<T: BitSet + Clone, const BITS: usize>(Option<(T, T)>);

impl<T: BitSet + Clone, const BITS: usize> SubsetIter<T, BITS> {
    pub fn new(superset: &T, subset_size: u32) -> Self {
        let Some(subset_size_minus_one) = subset_size.checked_sub(1) else {
            //return empty set
            return Self(Some((T::EMPTY, superset.clone())));
        };

        let next_set = match superset.nth(subset_size_minus_one) {
            Some(nth_element) => {
                let mut s = T::from_first_n(nth_element + 1);
                s.intersect_with(superset);
                s
            }

            None => {
                //not enough elements in the set - return an empty iterator
                return Self(None);
            }
        };
        let excluded_set = superset.with_except(&next_set);

        Self(Some((next_set, excluded_set)))
    }
}

impl<T: BitSet + Clone, const BITS: usize> core::iter::FusedIterator for SubsetIter<T, BITS> {}

impl<T: BitSet + Clone, const BITS: usize> Iterator for SubsetIter<T, BITS> {
    type Item = T;

    #[expect(warnings)]
    fn next(&mut self) -> Option<Self::Item> {
        let (next_set, excluded_set) = self.0.as_mut()?;
        let result = next_set.clone();
        let Some(first_index) = next_set.first() else {
            self.0 = None;
            return Some(result);
        };

        let Some(first_zero_index) = excluded_set.smallest_element_greater_than(first_index) else {
            self.0 = None;
            //we are finished
            return Some(result);
        };
        let closest_one_index = next_set
            .largest_element_less_than(first_zero_index)
            .unwrap_or_default();

        next_set.insert(first_zero_index);
        next_set.remove(closest_one_index);
        excluded_set.insert(closest_one_index);
        excluded_set.remove(first_zero_index);

        'clean_up: loop {
            let Some(b) = next_set.largest_element_less_than(closest_one_index) else {
                break 'clean_up;
            };
            let a = excluded_set.first().unwrap_or_default();
            if a < b {
                next_set.insert(a);
                next_set.remove(b);
                excluded_set.insert(b);
                excluded_set.remove(a);
            } else {
                break 'clean_up;
            }
        }

        Some(result)
    }

    fn is_sorted(self) -> bool
    where
        Self: Sized,
        Self::Item: PartialOrd,
    {
        true
    }

    fn min(self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        let (n, _e) = self.0?;
        Some(n)
    }

    //todo last, min, max
}

macro_rules! impl_iter_subsets {
    ($bit_set: ty, $bits:expr) => {
        impl $bit_set {
            #[must_use]
            pub fn iter_subsets(&self, subset_size: u32) -> SubsetIter<Self, $bits> {
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

    use crate::{BitSet8, bit_set_trait::BitSet};

    #[test]
    pub fn test_subsets_size_8() {
        let superset = BitSet8::ALL;

        assert_eq!(
            superset.iter_subsets(8).collect::<Vec<_>>(),
            vec![BitSet8::ALL]
        );
    }

    #[test]
    pub fn test_subsets_size_7() {
        let superset = BitSet8::ALL;

        assert_eq!(
            superset.iter_subsets(7).collect::<Vec<_>>(),
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

    pub const fn n_choose_k(n: u32, k: u32) -> u32 {
        let mut result = 1;
        let m = if k <= n - k { k } else { n - k };
        let mut i = 0;
        while i < m {
            result *= n - i;
            result /= i + 1;
            i += 1;
        }

        result
    }

    #[test]
    pub fn fuzz_test() {
        fn test_subsets(actual: &[BitSet8], superset: BitSet8, size: u32) {
            let expected_count = n_choose_k(superset.len_const(), size);

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

            let mut sorted = actual.to_vec();
            sorted.sort();

            let _assert_unique = sorted.into_iter().reduce(|prev, x| {
                assert_ne!(prev, x);
                x
            });
        }

        for bitset in 0..=u8::MAX {
            let bitset = BitSet8::from_inner_const(bitset);
            for size in 1..=bitset.len_const() {
                let subsets = bitset.iter_subsets(size).collect::<Vec<_>>();

                test_subsets(&subsets, bitset, size);
            }
        }
    }

    #[test]
    pub fn test_subsets_size_3() {
        let superset = BitSet8::from_inner(0b11011111);

        assert_eq!(
            superset.iter_subsets(3).collect::<Vec<_>>(),
            vec![
                BitSet8::from_inner_const(0b111),
                BitSet8::from_inner_const(0b1011),
                BitSet8::from_inner_const(0b1101),
                BitSet8::from_inner_const(0b1110),
                BitSet8::from_inner_const(0b10011),
                BitSet8::from_inner_const(0b10101),
                BitSet8::from_inner_const(0b10110),
                BitSet8::from_inner_const(0b11001),
                BitSet8::from_inner_const(0b11010),
                BitSet8::from_inner_const(0b11100),
                BitSet8::from_inner_const(0b1000011),
                BitSet8::from_inner_const(0b1000101),
                BitSet8::from_inner_const(0b1000110),
                BitSet8::from_inner_const(0b1001001),
                BitSet8::from_inner_const(0b1001010),
                BitSet8::from_inner_const(0b1001100),
                BitSet8::from_inner_const(0b1010001),
                BitSet8::from_inner_const(0b1010010),
                BitSet8::from_inner_const(0b1010100),
                BitSet8::from_inner_const(0b1011000),
                BitSet8::from_inner_const(0b10000011),
                BitSet8::from_inner_const(0b10000101),
                BitSet8::from_inner_const(0b10000110),
                BitSet8::from_inner_const(0b10001001),
                BitSet8::from_inner_const(0b10001010),
                BitSet8::from_inner_const(0b10001100),
                BitSet8::from_inner_const(0b10010001),
                BitSet8::from_inner_const(0b10010010),
                BitSet8::from_inner_const(0b10010100),
                BitSet8::from_inner_const(0b10011000),
                BitSet8::from_inner_const(0b11000001),
                BitSet8::from_inner_const(0b11000010),
                BitSet8::from_inner_const(0b11000100),
                BitSet8::from_inner_const(0b11001000),
                BitSet8::from_inner_const(0b11010000)
            ]
        );
    }

    #[test]
    pub fn test_subsets_size_2() {
        let superset = BitSet8::from_inner(0b01010101);

        assert_eq!(
            superset.iter_subsets(2).collect::<Vec<_>>(),
            vec![
                BitSet8::from_inner_const(0b00000101),
                BitSet8::from_inner_const(0b00010001),
                BitSet8::from_inner_const(0b00010100),
                BitSet8::from_inner_const(0b01000001),
                BitSet8::from_inner_const(0b01000100),
                BitSet8::from_inner_const(0b01010000),
            ]
        );
    }

    #[test]
    pub fn test_subsets_size_1() {
        let superset = BitSet8::from_inner(0b01010101);

        assert_eq!(
            superset.iter_subsets(1).collect::<Vec<_>>(),
            vec![
                BitSet8::from_inner_const(0b00000001),
                BitSet8::from_inner_const(0b00000100),
                BitSet8::from_inner_const(0b00010000),
                BitSet8::from_inner_const(0b01000000),
            ]
        );
    }

    #[test]
    pub fn test_oversize_subsets() {
        assert_eq!(
            BitSet8::from_inner(0b01010101)
                .iter_subsets(5)
                .collect::<Vec<_>>(),
            vec![]
        );
    }

    #[test]
    pub fn test_subsets_size_0() {
        assert_eq!(
            BitSet8::from_inner(0b01010101)
                .iter_subsets(0)
                .collect::<Vec<_>>(),
            vec![BitSet8::EMPTY]
        );

        assert_eq!(
            BitSet8::EMPTY.iter_subsets(0).collect::<Vec<_>>(),
            vec![BitSet8::EMPTY]
        );
    }
}
