use crate::{bit_set_shiftable::BitSetShiftable, SetElement};

#[derive(Debug, Clone, PartialEq)]
pub struct BitSetIterator<T: BitSetShiftable>(pub(crate) T);

impl<T: BitSetShiftable> Iterator for BitSetIterator<T> {
    type Item = SetElement;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let c = self.0.len() as usize;
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
        if (self.0.len() as usize) <= n {
            self.0 = T::EMPTY;
            return None;
        }
        #[allow(clippy::cast_possible_truncation)]
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
                self.0.shift_left((shift + n + 1) % T::MAX_COUNT);
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
        if self.0 == T::ALL {
            for v in 0..(T::MAX_COUNT) {
                accum = f(accum, v);
            }
        } else {
            while !self.0.is_empty() {
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
        if self.0 == T::ALL {
            total += (T::MAX_COUNT * (T::MAX_COUNT - 1)) / 2;
        } else {
            while !self.0.is_empty() {
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

impl<T: BitSetShiftable> ExactSizeIterator for BitSetIterator<T> {}

impl<T: BitSetShiftable> core::iter::FusedIterator for BitSetIterator<T> {}

impl<T: BitSetShiftable> DoubleEndedIterator for BitSetIterator<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_last()
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if (self.0.len() as usize) <= n {
            self.0 = T::EMPTY;
            return None;
        }

        #[allow(clippy::cast_possible_truncation)]
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
                let r = T::MAX_COUNT - (shift + n + 1);
                self.0.shift_right((shift + n + 1) % T::MAX_COUNT);

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
        let mut offset = T::MAX_COUNT;

        //special case - prevents overflow when right shifting

        if self.0 == T::ALL {
            //special case - prevents overflow when right shifting
            for v in (0..(T::MAX_COUNT)).rev() {
                accum = f(accum, v);
            }
        } else {
            while !self.0.is_empty() {
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
