use crate::bit_set_trait::BitSet;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum SubsetIter<T: BitSet + Clone> {
    Finished,
    Unfinished { next_set: T, excluded_set: T },
}

impl<T: BitSet + Clone> SubsetIter<T> {
    pub fn new(mut superset: T, subset_size: u32) -> Self {
        let Some(subset_size_minus_one) = subset_size.checked_sub(1) else {
            //return empty set
            return Self::Unfinished {
                next_set: T::EMPTY,
                excluded_set: superset,
            };
        };

        let next_set = match superset.nth(subset_size_minus_one) {
            Some(nth_element) => {
                let mut s = T::from_first_n(nth_element + 1);
                s.intersect_with(&superset);
                s
            }

            None => {
                //not enough elements in the set - return an empty iterator
                return Self::Finished;
            }
        };
        superset.except_with(&next_set);

        Self::Unfinished {
            next_set,
            excluded_set: superset,
        }
    }
}

impl<T: BitSet + Clone> core::iter::FusedIterator for SubsetIter<T> {}
impl<T: BitSet + Clone> core::iter::ExactSizeIterator for SubsetIter<T> {
    fn len(&self) -> usize {
        match self {
            SubsetIter::Finished => 0,
            SubsetIter::Unfinished {
                next_set,
                excluded_set,
            } => {
                let max = crate::n_choose_k::NChooseK::new(
                    next_set.count() + excluded_set.count(),
                    next_set.count(),
                )
                .value();

                let superset = next_set.with_union(excluded_set);
                let next_set_index = superset.index_of_subset(next_set);

                (max - next_set_index) as usize
            }
        }
    }
}

impl<T: BitSet + Clone> Iterator for SubsetIter<T> {
    type Item = T;

    #[expect(warnings)]
    fn next(&mut self) -> Option<Self::Item> {
        let Self::Unfinished {
            next_set,
            excluded_set,
        } = self
        else {
            return None;
        };
        let result = next_set.clone();
        let Some(first_index) = next_set.first() else {
            *self = Self::Finished;
            return Some(result);
        };

        let Some(first_zero_index) = excluded_set.smallest_element_greater_than(first_index) else {
            *self = Self::Finished;
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

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.len()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.len();
        (size, Some(size))
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
        let Self::Unfinished {
            next_set,
            excluded_set: _,
        } = self
        else {
            return None;
        };
        Some(next_set)
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        let Self::Unfinished {
            next_set,
            excluded_set,
        } = self
        else {
            return None;
        };
        let subset_size = next_set.count();
        let mut superset = next_set;
        superset.union_with(&excluded_set);
        let index = superset.count_subsets(subset_size).saturating_sub(1);
        let last_set = superset.get_subset(subset_size, index);
        return Some(last_set);
    }

    fn max(self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.last()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let SubsetIter::Unfinished {
            next_set,
            excluded_set,
        } = self
        else {
            return None;
        };
        let subset_size = next_set.count();
        let superset = next_set.with_union(excluded_set);
        let subset_count = superset.count_subsets(subset_size);
        let next_set_index = superset.clone().index_of_subset(next_set);
        let nth_set_index = next_set_index + n as u32;
        if nth_set_index >= subset_count {
            *self = Self::Finished
        } else {
            *next_set = superset.clone().get_subset(subset_size, nth_set_index);
            let mut superset = superset;
            superset.except_with(&next_set);
            *excluded_set = superset;
        }

        self.next()
    }
}

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

    #[test]
    pub fn fuzz_test() {
        fn test_subsets(actual: &[BitSet8], superset: BitSet8, size: u32) {
            let expected_count = superset.count_subsets(size);

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
    pub fn test_nth() {
        let superset = BitSet8::from_inner(0b11011111);
        let iter = superset.iter_subsets(3);
        let collected = iter.clone().collect::<Vec<_>>();
        let total_plus_1 = collected.len() + 1;
        for first_index in 0..(total_plus_1) {
            let s = total_plus_1 - first_index;
            let mut iter = iter.clone();
            let a = iter.nth(first_index);
            assert_eq!(a, collected.get(first_index).copied());
            for second_index in 0..s {
                let mut iter = iter.clone();
                let b = iter.nth(second_index);
                assert_eq!(b, collected.get(first_index + 1+ second_index).copied(), "F:{first_index} S: {second_index}");
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

    #[test]
    pub fn test_last_subset() {
        assert_eq!(
            BitSet8::from_inner(0b01010101).iter_subsets(3).max(),
            Some(BitSet8::from_inner_const(0b01010100))
        );

        assert_eq!(
            BitSet8::from_inner(0b01010101)
                .iter_subsets(3)
                .skip(4)
                .max(),
            None
        );

        assert_eq!(
            BitSet8::from_inner(0b01010101).iter_subsets(0).max(),
            Some(BitSet8::EMPTY)
        );

        assert_eq!(BitSet8::from_inner(0b01010101).iter_subsets(5).max(), None);
    }

    #[test]
    pub fn test_min_subset() {
        assert_eq!(
            BitSet8::from_inner(0b01010101)
                .iter_subsets(3)
                .skip(2)
                .min(),
            Some(BitSet8::from_inner_const(0b1010001))
        );

        assert_eq!(
            BitSet8::from_inner(0b01010101)
                .iter_subsets(3)
                .skip(4)
                .min(),
            None
        );
    }

    #[test]
    pub fn test_len_count_size_hint() {
        let mut iter = BitSet8::from_inner(0b11101111).iter_subsets(3);

        let mut expected_count = 35;
        loop {
            assert_eq!(expected_count, iter.len());
            assert_eq!(expected_count, iter.clone().count());
            assert_eq!((expected_count, Some(expected_count)), iter.size_hint());
            if iter.next().is_none() {
                break;
            }
            expected_count -= 1;
        }

        assert_eq!(expected_count, 0)
    }

    //#[test]
}
