use crate::{
    BitSet8, BitSet16, BitSet32, BitSet64, BitSet128, SetElement, shiftable::ShiftableBitSet,
};

macro_rules! impl_bit_set_iterator {
    ($name:ident, $inner: ty) => {


        impl IntoIterator for $inner {
            type Item = SetElement;

            type IntoIter = $name;

            fn into_iter(self) -> Self::IntoIter {
                $name(self)
            }
        }

        #[derive(Debug, Clone, PartialEq)]
        pub struct$name (pub(crate) $inner);

        impl Iterator for $name{
            type Item = SetElement;

            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                self.0.pop_const()
            }
            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                let c = self.0.len_const() as usize;
                (c, Some(c))
            }
            #[inline]
            fn count(self) -> usize
            where
                Self: Sized,
            {
                self.len()
            }
            #[inline]
            fn last(self) -> Option<Self::Item>
            where
                Self: Sized,
            {
                self.0.last_const()
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
                if (self.0.len_const() as usize) <= n {
                    self.0 = <$inner>::EMPTY;
                    return None;
                }
                #[expect(clippy::cast_possible_truncation)]
                let mut n = n as SetElement;
                let mut shift = 0;
                loop {
                    let tz = self.0.t_zeros();
                    self.0.shift_right(tz);
                    shift += tz;
                    let to = self.0.t_ones();
                    if let Some(new_n) = n.checked_sub(to) {
                        n = new_n;
                        self.0.shift_right(to);
                        shift += to;
                    } else {
                        self.0.shift_right(n + 1);
                        let r = shift + n;
                        self.0.shift_left((shift + n + 1) % <$inner>::CAPACITY);
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
                if self.0 == <$inner>::ALL {
                    for v in 0..(<$inner>::CAPACITY) {
                        accum = f(accum, v);
                    }
                } else {
                    while self.0 != <$inner>::EMPTY {
                        let tz = self.0.t_zeros();
                        self.0.shift_right(tz);
                        offset += tz;
                        let ones = self.0.t_ones();
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
                if self.0 == <$inner>::ALL {
                    total += (<$inner>::CAPACITY * (<$inner>::CAPACITY - 1)) / 2;
                } else {
                    while self.0 != <$inner>::EMPTY {
                        let zeros = self.0.t_zeros();
                        self.0.shift_right(zeros);
                        multiplier += zeros;
                        let ones = self.0.t_ones();
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

        impl ExactSizeIterator for $name{}
        impl core::iter::FusedIterator for $name{}

        impl DoubleEndedIterator for $name{
        fn next_back(&mut self) -> Option<Self::Item> {
            self.0.pop_last_const()
        }

        fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
            if (self.0.len_const() as usize) <= n {
                self.0 = <$inner>::EMPTY;
                return None;
            }

            #[expect(clippy::cast_possible_truncation)]
            let mut n = n as SetElement;

            let mut shift = 0;

            loop {
                let lz = self.0.l_zeros();
                self.0.shift_left(lz);
                shift += lz;
                let leading_ones = self.0.l_ones();
                if let Some(new_n) = n.checked_sub(leading_ones) {
                    n = new_n;
                    self.0.shift_left(leading_ones);
                    shift += leading_ones;
                } else {
                    self.0.shift_left(n + 1);
                    let r = <$inner>::CAPACITY - (shift + n + 1);
                    self.0.shift_right((shift + n + 1) % <$inner>::CAPACITY);

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
            let mut offset = <$inner>::CAPACITY;

            //special case - prevents overflow when right shifting

            if self.0 == <$inner>::ALL {
                //special case - prevents overflow when right shifting
                for v in (0..(<$inner>::CAPACITY)).rev() {
                    accum = f(accum, v);
                }
            } else {
                while self.0 != <$inner>::EMPTY {
                    let lz = self.0.l_zeros();
                    self.0.shift_left(lz);
                    offset -= lz;
                    let leading_ones = self.0.l_ones();
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
    };


}

impl_bit_set_iterator!(BitSetIterator8, BitSet8);
impl_bit_set_iterator!(BitSetIterator16, BitSet16);
impl_bit_set_iterator!(BitSetIterator32, BitSet32);
impl_bit_set_iterator!(BitSetIterator64, BitSet64);
impl_bit_set_iterator!(BitSetIterator128, BitSet128);

#[cfg(test)]
mod tests {
    use crate::{BitSet16, SetElement, finite::FiniteBitSet};

    #[test]
    fn test_is_sorted() {
        let set = BitSet16::ALL;
        assert!(set.into_iter().is_sorted());
    }

    #[test]
    fn test_count() {
        let set = BitSet16::ALL;

        let mut iter = set.into_iter();

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
        let iter = set.into_iter();
        assert_eq!(iter.last(), Some(14));
    }

    #[test]
    fn test_iter_max() {
        let set = BitSet16::from_fn(|x| x % 3 == 0 && x < 15);
        let iter = set.into_iter();
        let max = Iterator::max(iter);
        assert_eq!(max, Some(12));
    }

    #[test]
    fn test_iter_min() {
        let set = BitSet16::from_fn(|x| x > 6 && x % 3 == 0);
        let iter = set.into_iter();
        let min = Iterator::min(iter);
        assert_eq!(min, Some(9));
    }

    #[test]
    fn test_iter_nth() {
        let set = BitSet16::from_fn(|x| x % 3 == 0);
        let expected_set = Vec::from_iter((0..(BitSet16::CAPACITY)).filter(|x| x % 3 == 0));

        let mut iter = set.into_iter();
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

        let actual: Vec<u32> = set.into_iter().rev().collect();
        let expected: Vec<u32> = expected_set.into_iter().rev().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_iter_nth_back() {
        let set = BitSet16::from_fn(|x| x % 3 == 0);
        let expected_set = Vec::from_iter((0..(BitSet16::CAPACITY)).filter(|x| x % 3 == 0));

        let mut iter = set.into_iter();
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
        let iter = set.into_iter();
        let fold_result = iter.fold(13, |acc, x| acc + x);

        assert_eq!(fold_result, 34);

        let complete_set = BitSet16::ALL;

        assert_eq!(
            complete_set.into_iter().fold(Vec::new(), |mut vec, v| {
                vec.push(v);
                vec
            }),
            Vec::from_iter(0..(BitSet16::CAPACITY))
        );
    }

    #[test]
    fn test_iter_rfold() {
        let set = BitSet16::from_fn(|x| x % 7 == 0);
        let iter = set.into_iter();
        let fold_result = iter.rfold(13, |acc, x| acc + x);

        assert_eq!(fold_result, 34);

        let complete_set = BitSet16::ALL;

        assert_eq!(
            complete_set.into_iter().rfold(Vec::new(), |mut vec, v| {
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

        let sum: SetElement = set.into_iter().sum();
        let expected_sum: SetElement = expected_set.into_iter().sum();

        assert_eq!(sum, expected_sum);

        assert_eq!(
            BitSet16::ALL.into_iter().sum::<SetElement>(),
            (0u32..16).sum::<u32>()
        );
    }
}
