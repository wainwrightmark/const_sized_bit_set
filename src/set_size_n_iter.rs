use crate::{bit_set_trait::BitSet, finite::FiniteBitSet, shiftable::ShiftableBitSet};

#[derive(Debug, Clone, PartialEq)]
pub struct SetSizeNIter<T: BitSet + ShiftableBitSet + FiniteBitSet + Clone> {
    next_set: T,
}

impl<T: BitSet + ShiftableBitSet + FiniteBitSet + Clone> core::iter::FusedIterator
    for SetSizeNIter<T>
{
}

impl<T: BitSet + ShiftableBitSet + FiniteBitSet + Clone> Iterator for SetSizeNIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let next_set = self.next_set.clone();

        let leading_ones = self.next_set.leading_ones();
        self.next_set.shift_left(leading_ones);

        if self.next_set.is_empty() {
            if !next_set.is_empty() {
                return Some(next_set);
            }
            return None;
        }

        let leading_zeros = self.next_set.leading_zeros();

        self.next_set.shift_left(1);
        self.next_set.shift_left(leading_zeros);

        self.next_set.shift_right(leading_zeros);
        self.next_set.shift_right(leading_ones + 1);
        let mut new_ones = T::ALL;
        new_ones.shift_left(T::CAPACITY - (1 + leading_ones));
        new_ones.shift_right(leading_zeros);
        new_ones.shift_left(1);

        self.next_set.union_with(&new_ones);

        Some(next_set)
    }
}

impl<T: BitSet + ShiftableBitSet + FiniteBitSet + Clone> SetSizeNIter<T> {
    /// Returns `None` if the count is 0 or the maximum size of the set or greater
    #[must_use]
    pub fn try_new(element_count: u32) -> Option<Self> {
        if element_count == 0 {
            return None;
        }
        if element_count >= T::CAPACITY {
            return None;
        }

        let next_set = T::from_first_n(element_count);
        Some(Self { next_set })
    }
}

#[cfg(test)]
mod tests {
    use super::SetSizeNIter;
    use crate::{BitSet8, bit_set_trait::BitSet};
    use std::vec;

    #[test]
    pub fn test_set_size_1_iter() {
        let actual: Vec<_> = SetSizeNIter::<BitSet8>::try_new(1).unwrap().collect();
        let expected: Vec<BitSet8> = (0..8u32).map(|x| BitSet8::EMPTY.with_inserted(x)).collect();
        assert_eq!(expected, actual);
    }

    #[test]
    pub fn test_set_size_2_iter() {
        let actual: Vec<_> = SetSizeNIter::<BitSet8>::try_new(2).unwrap().collect();

        let mut expected: Vec<BitSet8> = vec![];

        for first in 0..8u32 {
            for second in (first + 1)..8u32 {
                let set = BitSet8::EMPTY.with_inserted(first).with_inserted(second);
                expected.push(set);
            }
        }

        assert_eq!(expected, actual);
    }

    #[test]
    pub fn test_set_size_0_iter() {
        assert_eq!(SetSizeNIter::<BitSet8>::try_new(0), None);
    }

    #[test]
    pub fn test_set_size_8_iter() {
        assert_eq!(SetSizeNIter::<BitSet8>::try_new(8), None);
    }
}
