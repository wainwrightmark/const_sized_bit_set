use crate::SetElement;
#[cfg(any(test, feature = "serde"))]
use serde::{Deserialize, Serialize};

macro_rules! define_bit_set_n {
    ($name:ident, $inner: ty, $iter_name:ident) => {
        #[must_use]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
        #[cfg_attr(any(test, feature = "serde"), derive(Serialize, Deserialize))]
        pub struct $name($inner);

        impl $name {
            pub const EMPTY: Self = Self(0);
            pub const ALL: Self = Self(<$inner>::MAX);
            pub const MAX_COUNT: SetElement = <$inner>::BITS;

            /// Returns the number of elements in the set
            #[must_use]
            #[inline]
            #[doc(alias = "count")]
            pub const fn len_const(&self) -> SetElement {
                self.0.count_ones()
            }

            /// The inner value of the set
            #[must_use]
            #[inline]
            pub const fn inner_const(&self) -> $inner {
                self.0
            }

            /// Creates a new set from an inner value
            #[must_use]
            #[inline]
            pub const fn from_inner_const(inner: $inner) -> Self {
                Self(inner)
            }

            /// Whether this set contains the element
            pub const fn contains_const(&self, element: SetElement) -> bool {
                (self.0 >> element) & 1 == 1
            }

            /// Whether two sets are equal
            #[inline]
            pub const fn eq_const(&self, rhs: &Self) -> bool {
                self.0 == rhs.0
            }

            /// Returns the negation of a set
            /// The negation contains exactly those elements which are not in the original set
            #[inline]
            pub const fn negate_const(&mut self) {
                self.0 = !self.0
            }

            /// Insert an element into the set
            /// Returns whether the element was inserted (it was not already present)
            #[inline]
            pub const fn insert_const(&mut self, element: SetElement) -> bool {
                let mask = 1 << element;
                let r = self.0 & mask == 0;

                self.0 |= mask;
                r
            }

            /// Remove an element from the set
            #[inline]
            pub const fn remove_const(&mut self, element: SetElement) -> bool {
                let mask = 1 << element;
                let r = self.0 & mask != 0;
                self.0 &= !mask;
                r
            }

            /// Create a set of the elements 0..n
            #[must_use]
            #[inline]
            pub const fn from_first_n_const(n: SetElement) -> Self {
                let inner = !(<$inner>::MAX << n);
                Self(inner)
            }

            /// Swap the bits at i and j
            #[inline]
            pub const fn swap_bits_const(&mut self, i: SetElement, j: SetElement) {
                let x = (self.0 >> i ^ self.0 >> j) & 1;
                self.0 ^= x << i | x << j;
            }

            #[inline]
            pub const fn intersect_with_const(&mut self, rhs: &Self) {
                self.0 &= rhs.0
            }

            pub const fn union_with_const(&mut self, rhs: &Self) {
                self.0 |= rhs.0
            }

            pub const fn except_with_const(&mut self, rhs: &Self) {
                let mut o = *rhs;
                o.negate_const();
                self.intersect_with_const(&o)
            }

            pub const fn symmetric_difference_with_const(&mut self, rhs: &Self) {
                self.0 ^= rhs.0
            }

            #[must_use]
            #[inline]
            pub const fn is_subset_const(&self, rhs: &Self) -> bool {
                let mut s = *self;
                s.intersect_with_const(rhs);
                s.eq_const(self)
            }

            #[must_use]
            #[inline]
            pub const fn is_superset_const(&self, rhs: &Self) -> bool {
                rhs.is_subset_const(self)
            }

            pub const fn overlaps_const(&self, rhs: &Self) -> bool {
                let mut s = *self;
                s.intersect_with_const(rhs);
                !s.eq_const(&Self::EMPTY)
            }

            /// Returns the first (minimum) element in this set
            #[must_use]
            #[inline]
            #[doc(alias = "min_const")]
            pub const fn first_const(&self) -> Option<SetElement> {
                if self.0 == 0 {
                    return None;
                }
                let element = self.0.trailing_zeros();

                return Some(element);
            }

            /// Returns the first (minimum) element in this set
            #[must_use]
            #[inline]
            #[doc(alias = "max_const")]
            pub const fn last_const(&self) -> Option<SetElement> {
                if self.0 == 0 {
                    return None;
                }
                let element = (Self::MAX_COUNT - 1) - self.0.leading_zeros();
                return Some(element);
            }

            /// The removes the first (smallest) element of the set and returns it
            /// Returns `None` if the set is empty
            #[must_use]
            #[inline]
            pub const fn pop_const(&mut self) -> Option<SetElement> {
                if self.0 == 0 {
                    return None;
                }
                let tz = self.0.trailing_zeros();

                let t = self.0 & (<$inner>::MIN.wrapping_sub(self.0));
                self.0 ^= t;

                return Some(tz);
            }

            /// Removes the last (biggest) element of the set and returns it
            /// Returns `None` if the set is empty
            #[must_use]
            #[inline]
            pub const fn pop_last_const(&mut self) -> Option<SetElement> {
                if self.0 == 0 {
                    return None;
                }
                let element = (Self::MAX_COUNT - 1) - self.0.leading_zeros();

                self.0 &= !(1 << element);
                return Some(element);
            }
        }

        impl Extend<SetElement> for $name {
            fn extend<T: IntoIterator<Item = SetElement>>(&mut self, iter: T) {
                for x in iter {
                    self.insert_const(x);
                }
            }
        }

        impl FromIterator<SetElement> for $name {
            fn from_iter<T: IntoIterator<Item = SetElement>>(iter: T) -> Self {
                let mut set = Self::default();
                set.extend(iter);
                set
            }
        }

        impl IntoIterator for $name {
            type Item = SetElement;

            type IntoIter = $iter_name;

            fn into_iter(self) -> Self::IntoIter {
                $iter_name(self)
            }
        }

        #[derive(Debug, Clone, PartialEq)]
        pub struct $iter_name($name);

        impl ExactSizeIterator for $iter_name {}

        impl core::iter::FusedIterator for $iter_name {}

        impl Iterator for $iter_name {
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
                    self.0 .0 = 0;
                    return None;
                }
                #[allow(clippy::cast_possible_truncation)]
                let mut n = n as SetElement;
                let mut shift = 0;
                loop {
                    let tz = self.0 .0.trailing_zeros();
                    self.0 .0 >>= tz;
                    shift += tz;
                    let to = self.0 .0.trailing_ones();
                    if let Some(new_n) = n.checked_sub(to) {
                        n = new_n;
                        self.0 .0 >>= to;
                        shift += to;
                    } else {
                        self.0 .0 >>= n + 1;
                        let r = shift + n;
                        self.0 .0 = self.0 .0.wrapping_shl(shift + n + 1);

                        return Some(r);
                    }
                }
            }

            #[inline]
            fn fold<B, F>(self, init: B, mut f: F) -> B
            where
                Self: Sized,
                F: FnMut(B, Self::Item) -> B,
            {
                let mut accum = init;

                let mut word = self.0 .0;
                let mut offset = 0;

                if word == <$inner>::MAX {
                    //special case - prevents overflow when right shifting
                    for v in 0..($name::MAX_COUNT) {
                        accum = f(accum, v);
                    }
                } else {
                    while word != 0 {
                        let tz = word.trailing_zeros();
                        word >>= tz;
                        offset += tz;
                        let trailing_ones = word.trailing_ones();
                        for _ in 0..trailing_ones {
                            accum = f(accum, offset);
                            offset += 1;
                        }
                        word >>= trailing_ones;
                    }
                }

                accum
            }

            #[inline]
            fn sum<S>(self) -> S
            where
                Self: Sized,
                S: core::iter::Sum<Self::Item>,
            {
                let mut total = 0u32;
                let word = self.0 .0;
                let mut value = word;
                let mut multiplier = 0;

                if self.0 == $name::ALL {
                    const MAX_COUNT: SetElement = ($name::MAX_COUNT * ($name::MAX_COUNT - 1)) / 2;
                    total += MAX_COUNT;
                } else {
                    while value != 0 {
                        let zeros = value.trailing_zeros();
                        value >>= zeros;
                        multiplier += zeros;
                        let ones = value.trailing_ones(); //there must be some or we wouldn't have shifted right
                        value >>= ones; //cannot overflow as we checked for full set

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

        impl DoubleEndedIterator for $iter_name {
            #[inline]
            fn next_back(&mut self) -> Option<Self::Item> {
                self.0.pop_last_const()
            }

            fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
                if (self.0.len_const() as usize) <= n {
                    self.0 .0 = 0;
                    return None;
                }

                #[allow(clippy::cast_possible_truncation)]
                let mut n = n as SetElement;

                let mut shift = 0;

                loop {
                    let lz = self.0 .0.leading_zeros();
                    self.0 .0 <<= lz;
                    shift += lz;
                    let leading_ones = self.0 .0.leading_ones();
                    if let Some(new_n) = n.checked_sub(leading_ones) {
                        n = new_n;
                        self.0 .0 <<= leading_ones;
                        shift += leading_ones;
                    } else {
                        self.0 .0 <<= n + 1;
                        let r = $name::MAX_COUNT - (shift + n + 1);

                        self.0 .0 = self.0 .0.wrapping_shr(shift + n + 1);

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
                let mut offset = $name::MAX_COUNT;

                //special case - prevents overflow when right shifting

                if self.0 .0 == <$inner>::MAX {
                    //special case - prevents overflow when right shifting
                    for v in (0..($name::MAX_COUNT)).rev() {
                        accum = f(accum, v);
                    }
                } else {
                    while self.0 .0 != 0 {
                        let lz = self.0 .0.leading_zeros();
                        self.0 .0 <<= lz;
                        offset -= lz;
                        let leading_ones = self.0 .0.leading_ones();
                        for _ in 0..leading_ones {
                            offset -= 1;
                            accum = f(accum, offset);
                        }
                        self.0 .0 <<= leading_ones;
                    }
                }

                accum
            }
        }
    };
}

define_bit_set_n!(BitSet8, u8, BitSet8Iter);
define_bit_set_n!(BitSet16, u16, BitSet16Iter);

#[cfg(test)]
mod tests {
    use crate::{bit_set_n::BitSet16, bit_set_trait::BitSetTrait, SetElement};

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
        let expected_set = Vec::from_iter((0..(BitSet16::MAX_COUNT)).filter(|x| x % 3 == 0));

        let mut iter = set.into_iter();
        let mut expected_iter = expected_set.into_iter();

        for n in [0, 1, 2, 0] {
            let expected = expected_iter.nth(n);
            let actual = iter.nth(n);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_iter_nth_back() {
        let set = BitSet16::from_fn(|x| x % 3 == 0);
        let expected_set = Vec::from_iter((0..(BitSet16::MAX_COUNT)).filter(|x| x % 3 == 0));

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
            Vec::from_iter(0..(BitSet16::MAX_COUNT))
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
            Vec::from_iter((0..(BitSet16::MAX_COUNT)).rev())
        );
    }

    #[test]
    fn test_sum() {
        let set = BitSet16::from_fn(|x| x % 7 == 0 || x % 4 == 0);
        let expected_set =
            Vec::from_iter((0..(BitSet16::MAX_COUNT)).filter(|x| x % 7 == 0 || x % 4 == 0));

        let sum: SetElement = set.into_iter().sum();
        let expected_sum = expected_set.into_iter().sum();

        assert_eq!(sum, expected_sum);

        assert_eq!(BitSet16::ALL.into_iter().sum::<SetElement>(), (0..16).sum());
    }

    #[test]
    fn test_bit_set16() {
        assert_eq!(BitSet16::from_inner(0b1101).len(), 3);

        assert_eq!(
            BitSet16::from_inner(0b1101).with_inserted(1).inner(),
            0b1111
        );

        assert_eq!(BitSet16::from_inner(0b1101).inner(), 0b1101);

        assert_eq!(BitSet16::from_fn(|x| x == 2), BitSet16::from_inner(0b0100));

        assert!(!BitSet16::from_inner(0b0100).is_empty());
        assert!(BitSet16::from_inner(0b0000).is_empty());

        let set1 = BitSet16::from_inner(0b1110);
        let negated = set1.with_negated();
        assert_eq!(set1.with_union(&negated), BitSet16::ALL);
        assert_eq!(set1.with_intersect(&negated), BitSet16::EMPTY);

        assert_eq!(
            BitSet16::from_inner(0b0010).with_inserted(2),
            BitSet16::from_inner(0b0110)
        );

        assert_eq!(
            BitSet16::from_inner(0b0110).with_removed(2),
            BitSet16::from_inner(0b0010)
        );

        assert_eq!(
            BitSet16::from_inner(0b0110)
                .with_bit_set(3, true)
                .with_bit_set(2, false),
            BitSet16::from_inner(0b1010)
        );

        assert_eq!(BitSet16::from_first_n(3), BitSet16::from_inner(0b111));

        assert_eq!(
            BitSet16::from_inner(0b10),
            BitSet16::from_inner(0b01).with_bits_swapped(0, 1)
        );

        assert_eq!(
            BitSet16::from_inner(0b001),
            BitSet16::from_inner(0b101).with_intersect(&BitSet16::from_inner(0b011))
        );

        assert_eq!(
            BitSet16::from_inner(0b111),
            BitSet16::from_inner(0b101).with_union(&BitSet16::from_inner(0b011))
        );

        assert_eq!(
            BitSet16::from_inner(0b0100),
            BitSet16::from_inner(0b0111).with_except(&BitSet16::from_inner(0b0011))
        );

        assert!(BitSet16::from_inner(0b0101).is_subset(&BitSet16::from_inner(0b1101)));

        assert!(BitSet16::from_inner(0b1101).is_superset(&BitSet16::from_inner(0b0101)));

        assert!(BitSet16::from_inner(0b100).contains(2));
        assert!(!BitSet16::from_inner(0b100).contains(1));

        assert_eq!(BitSet16::from_inner(0b1100).first(), Some(2));
        assert_eq!(BitSet16::from_inner(0b0000).first(), None);

        assert_eq!(BitSet16::from_inner(0b1100).last(), Some(3));
        assert_eq!(BitSet16::from_inner(0b0000).last(), None);

        let mut set = BitSet16::from_inner(0b1100);
        assert_eq!(set.pop(), Some(2));
        assert_eq!(set.pop(), Some(3));
        assert_eq!(set.pop(), None);

        let mut set = BitSet16::from_inner(0b1100);
        assert_eq!(set.pop_last(), Some(3));
        assert_eq!(set.pop_last(), Some(2));
        assert_eq!(set.pop_last(), None);

        assert_eq!(
            BitSet16::from_first_n(8).min_set_by_key(|x| x % 2),
            BitSet16::from_inner(0b01010101)
        );
    }
}