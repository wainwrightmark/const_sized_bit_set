use core::iter::FusedIterator;

use crate::{SetElement, finite::FiniteBitSet, prelude::BitSet, shiftable::ShiftableBitSet};

#[derive(Debug, Clone, PartialEq)]
pub struct BitSetIterator<Inner: BitSet + ShiftableBitSet + FiniteBitSet>( Inner);

impl<Inner: BitSet + ShiftableBitSet + FiniteBitSet> BitSetIterator<Inner> {
    pub const fn new(inner: Inner) -> Self {
        Self(inner)
    }
}

impl<Inner: BitSet + ShiftableBitSet + FiniteBitSet> Iterator for BitSetIterator<Inner> {
    type Item = SetElement;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let c = self.0.count() as usize;
        (c, Some(c))
    }
    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.0.count() as usize
    }
    #[inline]
    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.0.last()
    }
    #[inline]
    fn max(self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.last()
    }
    #[inline]
    fn min(mut self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.next()
    }
    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if (self.0.count() as usize) <= n {
            self.0 = Inner::EMPTY;
            return None;
        }
        #[expect(clippy::cast_possible_truncation)]
        let mut n = n as SetElement;
        let mut shift = 0;
        loop {
            let tz = self.0.trailing_zeros();
            self.0.shift_right(tz);
            shift += tz;
            let to = self.0.trailing_ones();
            if let Some(new_n) = n.checked_sub(to) {
                n = new_n;
                self.0.shift_right(to);
                shift += to;
            } else {
                self.0.shift_right(n + 1);
                let r = shift + n;
                self.0.shift_left((shift + n + 1) % Inner::CAPACITY);
                return Some(r);
            }
        }
    }
    #[inline]
    fn fold<B, F>(mut self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        let mut offset = 0;
        if self.0.is_all() {
            for v in 0..(Inner::CAPACITY) {
                accum = f(accum, v);
            }
        } else {
            while !self.0.is_empty() {
                let tz = self.0.trailing_zeros();
                self.0.shift_right(tz);
                offset += tz;
                let ones = self.0.trailing_ones();
                for _ in 0..ones {
                    accum = f(accum, offset);
                    offset += 1;
                }
                self.0.shift_right(ones);
            }
        }
        accum
    }
    #[inline]
    fn sum<S>(mut self) -> S
    where
        Self: Sized,
        S: core::iter::Sum<Self::Item>,
    {
        let mut total = 0u32;
        let mut multiplier = 0;
        if self.0.is_all() {
            total += (Inner::CAPACITY * (Inner::CAPACITY - 1)) / 2;
        } else {
            while !self.0.is_empty() {
                let zeros = self.0.trailing_zeros();
                self.0.shift_right(zeros);
                multiplier += zeros;
                let ones = self.0.trailing_ones();
                self.0.shift_right(ones);
                total += (ones * (ones + multiplier + multiplier - 1)) / 2;
                multiplier += ones;
            }
        }
        S::sum(core::iter::once(total))
    }
    fn is_sorted(self) -> bool
    where
        Self: Sized,
        Self::Item: PartialOrd,
    {
        true
    }
}

impl<Inner: BitSet + ShiftableBitSet + FiniteBitSet> ExactSizeIterator for BitSetIterator<Inner>{}
impl<Inner: BitSet + ShiftableBitSet + FiniteBitSet> FusedIterator for BitSetIterator<Inner>{}
impl<Inner: BitSet + ShiftableBitSet + FiniteBitSet> DoubleEndedIterator for BitSetIterator<Inner>{

    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_last()
    }
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if (self.0.count() as usize) <= n {
            self.0 = Inner::EMPTY;
            return None;
        }
        #[expect(clippy::cast_possible_truncation)]
        let mut n = n as SetElement;
        let mut shift = 0;
        loop {
            let lz = self.0.leading_zeros();
            self.0.shift_left(lz);
            shift += lz;
            let leading_ones = self.0.leading_ones();
            if let Some(new_n) = n.checked_sub(leading_ones) {
                n = new_n;
                self.0.shift_left(leading_ones);
                shift += leading_ones;
            } else {
                self.0.shift_left(n + 1);
                let r = Inner::CAPACITY - (shift + n + 1);
                self.0.shift_right((shift + n + 1) % Inner::CAPACITY);
                return Some(r);
            }
        }
    }
    fn rfold<B, F>(mut self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        let mut offset = Inner::CAPACITY;
        if self.0.is_all() {
            for v in (0..(Inner::CAPACITY)).rev() {
                accum = f(accum, v);
            }
        } else {
            while !self.0.is_empty() {
                let lz = self.0.leading_zeros();
                self.0.shift_left(lz);
                offset -= lz;
                let leading_ones = self.0.leading_ones();
                for _ in 0..leading_ones {
                    offset -= 1;
                    accum = f(accum, offset);
                }
                self.0.shift_left(leading_ones);
            }
        }
        accum
    }
}

#[cfg(test)]
mod tests {
    use crate::{BitSet16, SetElement, finite::FiniteBitSet, prelude::BitSet};

    #[test]
    fn test_is_sorted() {
        let set = BitSet16::ALL;
        assert!(set.iter().is_sorted());
    }

    #[test]
    fn test_count() {
        let set = BitSet16::ALL;

        let mut iter = set.iter();

        let mut expected_count = 16;
        while expected_count > 0 {
            assert_eq!(expected_count, iter.clone().count());
            let _ = iter.next();
            expected_count -= 1;
            assert_eq!(expected_count, iter.clone().count());

            let _ = iter.next_back();
            expected_count -= 1;
            assert_eq!(expected_count, iter.clone().count());
        }
    }

    #[test]
    fn test_iter_last() {
        let set = BitSet16::from_fn(|x| x % 7 == 0);
        let iter = set.iter();
        assert_eq!(iter.last(), Some(14));
    }

    #[test]
    fn test_iter_max() {
        let set = BitSet16::from_fn(|x| x % 3 == 0 && x < 15);
        let iter = set.iter();
        let max = Iterator::max(iter);
        assert_eq!(max, Some(12));
    }

    #[test]
    fn test_iter_min() {
        let set = BitSet16::from_fn(|x| x > 6 && x % 3 == 0);
        let iter = set.iter();
        let min = Iterator::min(iter);
        assert_eq!(min, Some(9));
    }

    #[test]
    fn test_iter_nth() {
        let set = BitSet16::from_fn(|x| x % 3 == 0);
        let expected_set = Vec::from_iter((0..(BitSet16::CAPACITY)).filter(|x| x % 3 == 0));

        let mut iter = set.iter();
        let mut expected_iter = expected_set.into_iter();

        for n in [0, 1, 2, 0] {
            let expected = expected_iter.nth(n);
            let actual = iter.nth(n);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_iter_reverse() {
        let set = BitSet16::from_fn(|x| x % 3 == 0);
        let expected_set = Vec::from_iter((0..(BitSet16::CAPACITY)).filter(|x| x % 3 == 0));

        let actual: Vec<u32> = set.iter().rev().collect();
        let expected: Vec<u32> = expected_set.into_iter().rev().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_iter_nth_back() {
        let set = BitSet16::from_fn(|x| x % 3 == 0);
        let expected_set = Vec::from_iter((0..(BitSet16::CAPACITY)).filter(|x| x % 3 == 0));

        let mut iter = set.iter();
        let mut expected_iter = expected_set.into_iter();

        for n in [0, 1, 10, 2] {
            let expected = expected_iter.nth_back(n);
            let actual = iter.nth_back(n);

            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_iter_fold() {
        let set = BitSet16::from_fn(|x| x % 7 == 0);
        let iter = set.iter();
        let fold_result = iter.fold(13, |acc, x| acc + x);

        assert_eq!(fold_result, 34);

        let complete_set = BitSet16::ALL;

        assert_eq!(
            complete_set.iter().fold(Vec::new(), |mut vec, v| {
                vec.push(v);
                vec
            }),
            Vec::from_iter(0..(BitSet16::CAPACITY))
        );
    }

    #[test]
    fn test_iter_rfold() {
        let set = BitSet16::from_fn(|x| x % 7 == 0);
        let iter = set.iter();
        let fold_result = iter.rfold(13, |acc, x| acc + x);

        assert_eq!(fold_result, 34);

        let complete_set = BitSet16::ALL;

        assert_eq!(
            complete_set.iter().rfold(Vec::new(), |mut vec, v| {
                vec.push(v);
                vec
            }),
            Vec::from_iter((0..(BitSet16::CAPACITY)).rev())
        );
    }

    #[test]
    fn test_sum() {
        let set = BitSet16::from_fn(|x| x % 7 == 0 || x % 4 == 0);
        let expected_set =
            Vec::from_iter((0..(BitSet16::CAPACITY)).filter(|x| x % 7 == 0 || x % 4 == 0));

        let sum: SetElement = set.iter().sum();
        let expected_sum: SetElement = expected_set.into_iter().sum();

        assert_eq!(sum, expected_sum);

        assert_eq!(
            BitSet16::ALL.iter().sum::<SetElement>(),
            (0u32..16).sum::<u32>()
        );
    }
}
