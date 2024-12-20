use crate::n_choose_k::n_choose_k;
use core::fmt::{Debug, Write};
use core::iter::FusedIterator;
#[cfg(any(test, feature = "serde"))]
use serde::{Deserialize, Serialize};

/// A set whose members are unsigned integers in `0..(64 * WORDS)`
/// Most operations are O(1)
///
/// Sets are not ordered lexicographically
/// Set `b` is considered greater than set `a` if the largest element that is contained in `a | b` but not `a & b` is in `b`.
/// Therefore sets are ordered like [], [0], [1], [0,1], [2], [0,2], [1,2], [0,1,2]
#[must_use]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(any(test, feature = "serde"), derive(Serialize, Deserialize))]
pub struct BitSetArray<const WORDS: usize>(
    #[cfg_attr(any(test, feature = "serde"), serde(with = "serde_arrays"))] [u64; WORDS],
);

impl<const WORDS: usize> core::fmt::Display for BitSetArray<WORDS> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_char('[')?;
        let mut write_commas: bool = false;
        for x in self.into_iter() {
            if write_commas {
                f.write_char(',')?;
                f.write_char(' ')?;
            } else {
                write_commas = true;
            }
            core::fmt::Display::fmt(&x, f)?;
        }

        f.write_char(']')?;
        Ok(())
    }
}

impl<const WORDS: usize> Default for BitSetArray<WORDS> {
    fn default() -> Self {
        Self::EMPTY
    }
}

const WORD_BITS: usize = u64::BITS as usize;

impl<const WORDS: usize> BitSetArray<WORDS> {
    /// The set where all tiles are missing
    pub const EMPTY: Self = { Self([0; WORDS]) };

    /// The set where all tiles are present
    pub const ALL: Self = { Self::EMPTY.negate() };

    pub const LAST_WORD: usize = WORDS - 1;

    #[inline]
    #[must_use]
    pub fn from_fn<F: FnMut(usize) -> bool>(mut cb: F) -> Self {
        let mut result = Self::default();
        for x in (0..(WORDS * (WORD_BITS))).filter(|x| cb(*x)) {
            result.insert(x);
        }

        result
    }

    #[must_use]
    #[inline]
    pub const fn into_inner(self) -> [u64; WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_inner(inner: [u64; WORDS]) -> Self {
        Self(inner)
    }

    #[must_use]
    #[inline]
    pub const fn eq(&self, rhs: &Self) -> bool {
        let mut word = 0;
        while word < WORDS {
            if self.0[word] != rhs.0[word] {
                return false;
            }
            word += 1;
        }
        true
    }

    #[must_use]
    #[inline]
    pub const fn is_empty(self) -> bool {
        self.eq(&Self::EMPTY)
    }

    /// Sets the bit at `index` to `bit`
    ///
    /// PANICS if index is out of range
    #[inline]
    pub const fn set_bit(&mut self, index: usize, bit: bool) {
        if bit {
            self.insert(index);
        } else {
            self.remove(index);
        }
    }

    /// Adds `value` to the set.
    ///
    /// Returns whether `value` was newly inserted.
    ///
    /// PANICS if `value` is out of range
    #[inline]
    pub const fn insert(&mut self, value: usize) -> bool {
        let word = value / WORD_BITS;
        #[allow(clippy::cast_possible_truncation)]
        let shift = (value % WORD_BITS) as u32;
        let mask = 1u64 << shift;
        let r = self.0[word] & mask == 0;

        self.0[word] |= mask;
        r
    }

    /// If the set contains `value`, removes it from the set.
    /// Returns whether such an element was present.
    ///
    /// PANICS if `value` is out of range
    #[inline]
    pub const fn remove(&mut self, value: usize) -> bool {
        let word = value / WORD_BITS;
        #[allow(clippy::cast_possible_truncation)]
        let shift = (value % WORD_BITS) as u32;
        let mask = 1u64 << shift;
        let r = self.0[word] & mask != 0;

        self.0[word] &= !mask;
        r
    }

    /// Returns a copy of `self` with the bit at `index` set to `bit`
    ///
    /// PANICS if index is out of range
    #[must_use]
    #[inline]
    pub const fn with_bit_set(&self, index: usize, bit: bool) -> Self {
        if bit {
            self.with_inserted(index)
        } else {
            self.with_removed(index)
        }
    }

    /// PANICS if value is out of range
    #[must_use]
    #[inline]
    pub const fn with_inserted(&self, value: usize) -> Self {
        let word = value / WORD_BITS;
        #[allow(clippy::cast_possible_truncation)]
        let shift = (value % WORD_BITS) as u32;

        let mut arr = self.0;
        arr[word] = self.0[word] | (1u64 << shift);

        Self(arr)
    }

    /// PANICS if value is out of range
    #[must_use]
    #[inline]
    pub const fn with_removed(&self, value: usize) -> Self {
        let word = value / WORD_BITS;
        #[allow(clippy::cast_possible_truncation)]
        let shift = (value % WORD_BITS) as u32;

        let mut arr = self.0;
        arr[word] = self.0[word] & !(1u64 << shift);

        Self(arr)
    }

    #[must_use]
    #[inline]
    #[doc(alias = "get_bit")]
    pub const fn contains(&self, index: usize) -> bool {
        let word_index = index / WORD_BITS;
        #[allow(clippy::cast_possible_truncation)]
        let shift = (index % WORD_BITS) as u32;

        if word_index >= WORDS {
            return false;
        }
        let word = self.0[word_index];

        (word >> shift) & 1 == 1
    }

    #[must_use]
    #[inline]
    pub const fn count(&self) -> u32 {
        let mut count: u32 = 0;
        let mut word = 0;
        while word < WORDS {
            count += self.0[word].count_ones();
            word += 1;
        }

        count
    }

    #[must_use]
    #[inline]
    pub const fn intersect(&self, rhs: &Self) -> Self {
        let mut arr = self.0;
        let mut word = 0;
        while word < WORDS {
            let r = rhs.0[word];
            arr[word] &= r;
            word += 1;
        }

        Self(arr)
    }

    #[must_use]
    #[inline]
    pub const fn union(&self, rhs: &Self) -> Self {
        let mut arr = self.0;
        let mut word = 0;
        while word < WORDS {
            let r = rhs.0[word];
            arr[word] |= r;
            word += 1;
        }

        Self(arr)
    }

    #[must_use]
    #[inline]
    pub const fn is_subset(&self, rhs: &Self) -> bool {
        self.intersect(rhs).eq(self)
    }

    #[must_use]
    #[inline]
    pub const fn is_superset(&self, rhs: &Self) -> bool {
        rhs.is_subset(self)
    }

    /// Returns a new set containing all elements which belong to one set but not both
    #[must_use]
    #[inline]
    pub const fn symmetric_difference(&self, rhs: &Self) -> Self {
        let mut arr = self.0;
        let mut word = 0;
        while word < WORDS {
            let r = rhs.0[word];
            arr[word] ^= r;
            word += 1;
        }

        Self(arr)
    }

    #[must_use]
    #[inline]
    pub const fn negate(&self) -> Self {
        let mut arr = [0; WORDS];
        let mut word = 0;
        while word < WORDS {
            arr[word] = !self.0[word];
            word += 1;
        }

        Self(arr)
    }

    /// The first (minimum) element in this set
    #[must_use]
    #[inline]
    #[doc(alias = "min")]
    pub const fn first(&self) -> Option<usize> {
        let mut word = 0;
        while word < WORDS {
            let tz = self.0[word].trailing_zeros();
            if tz < u64::BITS {
                return Some(tz as usize + (word * (WORD_BITS)));
            }
            word += 1;
        }
        None
    }

    /// The last (maximum) element in this set
    #[must_use]
    #[inline]
    #[doc(alias = "max")]
    pub const fn last(&self) -> Option<usize> {
        let mut word = Self::LAST_WORD;

        loop {
            if let Some(index) = (u64::BITS - 1).checked_sub(self.0[word].leading_zeros()) {
                let r = index as usize + (word * (WORD_BITS));
                return Some(r);
            }
            if let Some(nw) = word.checked_sub(1) {
                word = nw;
            } else {
                return None;
            }
        }
    }

    /// The removes the first (smallest) element of the set and returns it
    /// Returns `None` if the set is empty
    #[must_use]
    #[inline]
    pub fn pop(&mut self) -> Option<usize> {
        for word_index in 0..=Self::LAST_WORD {
            let word = self.0[word_index];
            if word != 0 {
                let tz = word.trailing_zeros();
                let r = tz as usize + (word_index * (WORD_BITS));
                let t = word & (0u64.wrapping_sub(word));
                self.0[word_index] ^= t;

                return Some(r);
            }
        }
        None
    }

    /// Removes the last (biggest) element of the set and returns it
    /// Returns `None` if the set is empty
    #[must_use]
    #[inline]
    pub fn pop_last(&mut self) -> Option<usize> {
        let mut word_index = Self::LAST_WORD;

        loop {
            let word = self.0[word_index];

            if word != 0 {
                let index = (u64::BITS - 1) - word.leading_zeros();
                let r = index as usize + (word_index * (WORD_BITS));
                self.0[word_index] &= !(1u64 << index);
                return Some(r);
            }

            if let Some(nw) = word_index.checked_sub(1) {
                word_index = nw;
            } else {
                return None;
            }
        }
    }

    // /// Return the index of the nth element.
    // /// Returns `None` if there are fewer than n+1 elements
    // #[must_use]
    // #[inline]
    // pub fn nth(&self, n: u32)-> Option<usize>{
    //     if self.
    // }

    //todo find a faster way to do this
    fn subset_index_to_members(&self, subset_size: u32, index: u32, member_count: u32) -> Self {
        let mut n_c_k = crate::n_choose_k::NChooseK::new(self.count(), subset_size, member_count);

        // essentially reverse the order
        let mut index = n_c_k.result() - (index + 1);
        let mut new_set = Self::EMPTY;
        n_c_k = match n_c_k.try_decrement_k() {
            Some(r) => r,
            None => {
                return new_set;
            }
        };

        n_c_k = match n_c_k.try_decrement_n() {
            Some(r) => r,
            None => {
                return new_set;
            }
        };

        let mut set_remaining = *self;

        while let Some(next) = set_remaining.pop_last() {
            //let number_containing = n_choose_k(remaining_count - 1, remaining_needed - 1);
            if let Some(new_index) = index.checked_sub(n_c_k.result()) {
                index = new_index;
            } else {
                new_set.set_bit(next, true);
                match n_c_k.try_decrement_k() {
                    Some(r) => n_c_k = r,
                    None => return new_set,
                }
            }
            match n_c_k.try_decrement_n() {
                Some(r) => n_c_k = r,
                None => return new_set.union(&set_remaining),
            }
        }

        new_set
    }

    #[must_use]
    pub fn iter_subsets(
        &self,
        subset_size: u32,
    ) -> impl FusedIterator<Item = Self>
           + DoubleEndedIterator
           + ExactSizeIterator
           + Debug
           + Clone
           + 'static {
        let member_count = n_choose_k(self.count(), subset_size);
        let s = *self;

        (0..member_count)
            .map(move |index| s.subset_index_to_members(subset_size, index, member_count))
    }
}

impl<const WORDS: usize> Extend<usize> for BitSetArray<WORDS> {
    fn extend<T: IntoIterator<Item = usize>>(&mut self, iter: T) {
        *self = iter.into_iter().fold(*self, |acc, v| acc.with_inserted(v));
    }
}

impl<const WORDS: usize> FromIterator<usize> for BitSetArray<WORDS> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = usize>>(iter: T) -> Self {
        iter.into_iter()
            .fold(Self::default(), |acc, v| acc.with_inserted(v))
    }
}

impl<const WORDS: usize> IntoIterator for BitSetArray<WORDS> {
    type Item = usize;

    type IntoIter = BitSetIter<WORDS>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        BitSetIter { inner: self }
    }
}

#[must_use]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitSetIter<const WORDS: usize> {
    inner: BitSetArray<WORDS>,
}

impl<const WORDS: usize> ExactSizeIterator for BitSetIter<WORDS> {
    fn len(&self) -> usize {
        self.inner.count() as usize
    }
}
impl<const WORDS: usize> FusedIterator for BitSetIter<WORDS> {}

impl<const WORDS: usize> Iterator for BitSetIter<WORDS> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.pop()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let c = self.len();
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
        self.inner.last()
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
        let mut word_index = 0;
        #[allow(clippy::cast_possible_truncation)]
        let mut n = n as u32;
        while word_index < WORDS {
            if let Some(new_n) = n.checked_sub(self.inner.0[word_index].count_ones()) {
                n = new_n;
                self.inner.0[word_index] = 0;
                word_index += 1;
                //continue loop
            } else {
                let mut shift = 0;
                let mut word = self.inner.0[word_index];
                loop {
                    let tz = word.trailing_zeros();
                    word >>= tz;
                    shift += tz;
                    let to = word.trailing_ones();
                    if let Some(new_n) = n.checked_sub(to) {
                        n = new_n;
                        word >>= to;
                        shift += to;
                    } else {
                        word >>= n + 1;
                        let r = (shift + n) as usize + (word_index * (WORD_BITS));

                        let word = word.wrapping_shl(shift + n + 1);
                        self.inner.0[word_index] = word;

                        return Some(r);
                    }
                }
            }
        }
        None
    }

    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;

        for index in 0..WORDS {
            let mut word = self.inner.0[index];
            let mut offset = index * (WORD_BITS);
            if word == u64::MAX {
                for v in offset..(offset + (WORD_BITS)) {
                    accum = f(accum, v);
                }
            } else {
                while word != 0 {
                    let tz = word.trailing_zeros();
                    word >>= tz;
                    offset += tz as usize;
                    let trailing_ones = word.trailing_ones();
                    for _ in 0..trailing_ones {
                        accum = f(accum, offset);
                        offset += 1;
                    }
                    word >>= trailing_ones;
                }
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

        for index in 0..WORDS {
            let word = self.inner.0[index];
            #[allow(clippy::cast_possible_truncation)]
            let mut multiplier = index as u32 * u64::BITS;

            if word == u64::MAX {
                total += word.count_ones() * multiplier;
                total += 2016; //sum of 0..64
            } else {
                let mut value = word;

                while value != 0 {
                    let zeros = value.trailing_zeros();
                    value >>= zeros;
                    multiplier += zeros;
                    let ones = value.trailing_ones(); //there must be some or we wouldn't have shifted right
                    value >>= ones; //cannot overflow as we checked for u64::MAX

                    total += (ones * (ones + multiplier + multiplier - 1)) / 2;

                    multiplier += ones;
                }
            };
        }

        S::sum(core::iter::once(total as usize))
    }

    fn is_sorted(self) -> bool
    where
        Self: Sized,
        Self::Item: PartialOrd,
    {
        true
    }

    //todo find a fast way to do Sum
    //todo find a fast way to do Product
}

impl<const WORDS: usize> DoubleEndedIterator for BitSetIter<WORDS> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.pop_last()
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let mut word_index = BitSetArray::<WORDS>::LAST_WORD;
        #[allow(clippy::cast_possible_truncation)]
        let mut n = n as u32;
        loop {
            if let Some(new_n) = n.checked_sub(self.inner.0[word_index].count_ones()) {
                n = new_n;
                self.inner.0[word_index] = 0;
                word_index = word_index.checked_sub(1)?;
            } else {
                let mut shift = 0;
                let mut word = self.inner.0[word_index];
                loop {
                    let lz = word.leading_zeros();
                    word <<= lz;
                    shift += lz;
                    let leading_ones = word.leading_ones();
                    if let Some(new_n) = n.checked_sub(leading_ones) {
                        n = new_n;
                        word <<= leading_ones;
                        shift += leading_ones;
                    } else {
                        word <<= n + 1;
                        let r = (u64::BITS - (shift + n + 1)) as usize + (word_index * (WORD_BITS));

                        word = word.wrapping_shr(shift + n + 1);
                        self.inner.0[word_index] = word;

                        return Some(r);
                    }
                }
            }
        }
    }

    fn rfold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        let mut index = WORDS;
        for mut word in self.inner.0.into_iter().rev() {
            let mut offset = index * (WORD_BITS);

            if word == u64::MAX {
                for v in ((offset - (WORD_BITS))..offset).rev() {
                    accum = f(accum, v);
                }
            } else {
                while word != 0 {
                    let lz = word.leading_zeros();
                    word <<= lz;
                    offset -= lz as usize;
                    let leading_ones = word.leading_ones();
                    for _ in 0..leading_ones {
                        offset -= 1;
                        accum = f(accum, offset);
                    }
                    word <<= leading_ones;
                }
            }
            index -= 1;
        }
        accum
    }
}

#[cfg(test)]
pub mod tests {
    use crate::bit_set_array::BitSetArray;
    use crate::n_choose_k::*;
    use std::collections::BTreeSet;

    #[test]
    pub fn from_fn_4() {
        let evens = BitSetArray::<4>::from_fn(|x| x % 2 == 0);

        assert_eq!(128, evens.count());
        let iter = evens.into_iter();
        assert_eq!(iter.len(), 128);

        let items: Vec<usize> = iter.collect();
        let expected: Vec<usize> = (0..128usize).map(|x| x * 2).collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn from_iter_4() {
        let expected: Vec<usize> = (0..52usize).map(|x| x * 5).collect();

        let set = BitSetArray::<4>::from_iter(expected.iter().copied());

        assert_eq!(52, set.count());

        let iter = set.into_iter();
        assert_eq!(iter.len(), 52);
        assert_eq!(iter.size_hint(), (52, Some(52)));

        let items: Vec<usize> = iter.collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn extend_4() {
        let multiples_of_5: Vec<usize> = (0..52usize).map(|x| x * 5).collect();
        let multiples_of_4: Vec<usize> = (0..64usize).map(|x| x * 4).collect();

        let mut set = BitSetArray::<4>::from_iter(multiples_of_5.iter().copied());
        set.extend(multiples_of_4);

        assert_eq!(103, set.count());

        let expected = BitSetArray::<4>::from_fn(|x| x % 4 == 0 || x % 5 == 0);

        assert_eq!(set, expected);
    }

    #[test]
    pub fn reverse_iter_4() {
        let expected: Vec<usize> = (0..52usize).map(|x| x * 5).rev().collect();

        let set = BitSetArray::<4>::from_iter(expected.iter().copied());

        assert_eq!(52, set.count());

        let iter = set.into_iter();
        assert_eq!(iter.len(), 52);
        assert_eq!(iter.size_hint(), (52, Some(52)));

        let items: Vec<usize> = iter.rev().collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn is_empty_4() {
        let mut my_set = BitSetArray::<4>::EMPTY;

        assert!(my_set.is_empty());

        my_set.set_bit(255, true);

        assert!(!my_set.is_empty());

        my_set.set_bit(255, false);

        assert!(my_set.is_empty());
    }

    #[test]
    pub fn from_inner_4() {
        let evens = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        let inner = evens.into_inner();

        assert_eq!(inner, [6_148_914_691_236_517_205; 4]);
        let again = BitSetArray::from_inner(inner);

        assert_eq!(evens, again);

        let eq = evens.eq(&again);

        assert!(eq);
    }

    #[test]
    pub fn contains_4() {
        let my_set = BitSetArray::<4>::from_fn(|x| x % 2 == 0);

        for x in 0..260 {
            let value = my_set.contains(x);

            assert_eq!(x % 2 == 0 && x < 256, value);
        }
    }

    #[test]
    pub fn set_bit_4() {
        let mut my_set = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        my_set.set_bit(1, true);
        my_set.set_bit(1, true); //set the bit twice to test that
        my_set.set_bit(65, true);

        my_set.set_bit(2, false);
        my_set.set_bit(64, false);

        let mut expected: BTreeSet<usize> = (0..128usize).map(|x| x * 2).collect();
        expected.insert(1);
        expected.insert(65);
        expected.remove(&2);
        expected.remove(&64);

        let actual: Vec<_> = my_set.into_iter().collect();
        let expected: Vec<_> = expected.into_iter().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    pub fn insert_and_remove_bit_4() {
        let mut my_set = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        assert!(my_set.insert(1));
        assert!(!my_set.insert(1));
        assert!(my_set.insert(65));

        assert!(my_set.remove(2));
        assert!(my_set.remove(64));

        let mut expected: BTreeSet<usize> = (0..128usize).map(|x| x * 2).collect();
        expected.insert(1);
        expected.insert(65);
        expected.remove(&2);
        expected.remove(&64);

        let actual: Vec<_> = my_set.into_iter().collect();
        let expected: Vec<_> = expected.into_iter().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    pub fn with_bit_set_4() {
        let my_set = BitSetArray::<4>::from_fn(|x| x % 2 == 0)
            .with_bit_set(1, true)
            .with_bit_set(1, true) //set the bit twice to test that
            .with_bit_set(65, true)
            .with_bit_set(2, false)
            .with_bit_set(64, false);

        let mut expected: BTreeSet<usize> = (0..128usize).map(|x| x * 2).collect();
        expected.insert(1);
        expected.insert(65);
        expected.remove(&2);
        expected.remove(&64);

        let actual: Vec<_> = my_set.into_iter().collect();
        let expected: Vec<_> = expected.into_iter().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    pub fn union_4() {
        let multiples_of_2 = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSetArray::<4>::from_fn(|x| x % 5 == 0);
        let multiples_of_2_or_5 = BitSetArray::<4>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let union = multiples_of_2.union(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5, union);
    }

    #[test]
    pub fn intersect_4() {
        let multiples_of_2 = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSetArray::<4>::from_fn(|x| x % 5 == 0);
        let multiples_of_10 = BitSetArray::<4>::from_fn(|x| x % 10 == 0);
        let multiples_of_6 = BitSetArray::<4>::from_fn(|x| x % 6 == 0);

        let intersection = multiples_of_2.intersect(&multiples_of_5);

        assert_eq!(multiples_of_10, intersection);

        assert!(intersection.is_subset(&multiples_of_2));
        assert!(intersection.is_subset(&multiples_of_5));
        assert!(intersection.is_subset(&multiples_of_10));

        assert!(!intersection.is_superset(&multiples_of_2));
        assert!(!intersection.is_superset(&multiples_of_5));
        assert!(intersection.is_superset(&multiples_of_10));

        assert!(!multiples_of_2.is_subset(&intersection));
        assert!(!multiples_of_5.is_subset(&intersection));
        assert!(intersection.is_subset(&intersection));

        assert!(multiples_of_2.is_superset(&intersection));
        assert!(multiples_of_5.is_superset(&intersection));
        assert!(intersection.is_superset(&intersection));

        assert!(!intersection.is_subset(&multiples_of_6));
        assert!(!intersection.is_superset(&multiples_of_6));
    }

    #[test]
    pub fn symmetric_difference_4() {
        let multiples_of_2 = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSetArray::<4>::from_fn(|x| x % 5 == 0);

        let multiples_of_2_or_5_but_not_10 =
            BitSetArray::<4>::from_fn(|x| x % 10 != 0 && (x % 2 == 0 || x % 5 == 0));

        let sym_diff = multiples_of_2.symmetric_difference(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5_but_not_10, sym_diff);
    }

    #[test]
    pub fn negate_4() {
        let evens = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        let odds = BitSetArray::<4>::from_fn(|x| x % 2 == 1);

        let negated_evens = evens.negate();

        assert_eq!(negated_evens, odds);
    }

    #[test]
    fn test_serde_empty_4() {
        use serde_test::*;
        let map = BitSetArray::<4>::EMPTY;

        assert_tokens(
            &map,
            &[
                Token::NewtypeStruct {
                    name: "BitSetArray",
                },
                Token::Tuple { len: 4 },
                Token::U64(0),
                Token::U64(0),
                Token::U64(0),
                Token::U64(0),
                Token::TupleEnd,
            ],
        );
    }

    #[test]
    fn test_serde_4() {
        use serde_test::*;
        let map = BitSetArray::<4>::from_fn(|x| x % 2 == ((x / 64) % 2));

        assert_tokens(
            &map,
            &[
                Token::NewtypeStruct {
                    name: "BitSetArray",
                },
                Token::Tuple { len: 4 },
                Token::U64(6_148_914_691_236_517_205),
                Token::U64(12_297_829_382_473_034_410),
                Token::U64(6_148_914_691_236_517_205),
                Token::U64(12_297_829_382_473_034_410),
                Token::TupleEnd,
            ],
        );
    }

    #[test]
    fn test_first4() {
        let mut set = BitSetArray::<4>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..256).filter(|x| x % 2 == 0 || x % 5 == 0).collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(first) = set.first() {
            set.set_bit(first, false);
            actual.push(first);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_last4() {
        let mut set = BitSetArray::<4>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..256)
            .filter(|x| x % 2 == 0 || x % 5 == 0)
            .rev()
            .collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(last) = set.last() {
            set.set_bit(last, false);
            actual.push(last);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_pop4() {
        let mut set = BitSetArray::<4>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..256).filter(|x| x % 2 == 0 || x % 5 == 0).collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(first) = set.pop() {
            actual.push(first);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_pop_last4() {
        let mut set = BitSetArray::<4>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..256)
            .filter(|x| x % 2 == 0 || x % 5 == 0)
            .rev()
            .collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(last) = set.pop_last() {
            actual.push(last);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_iter_last4() {
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0);
        let iter = set.into_iter();
        assert_eq!(iter.last(), Some(252));
    }

    #[test]
    fn test_iter_max4() {
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0 && x < 140);
        let iter = set.into_iter();
        let max = Iterator::max(iter);
        assert_eq!(max, Some(133));
    }

    #[test]
    fn test_iter_min4() {
        let set = BitSetArray::<4>::from_fn(|x| x > 64 && x % 7 == 0);
        let iter = set.into_iter();
        let min = Iterator::min(iter);
        assert_eq!(min, Some(70));
    }

    #[test]
    fn test_iter_nth_4() {
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0);
        let expected_set = Vec::from_iter((0..256usize).filter(|x| x % 7 == 0));

        let mut iter = set.into_iter();
        let mut expected_iter = expected_set.into_iter();

        for n in [0, 1, 10, 2, 3, 0, 0, 2, 3] {
            let expected = expected_iter.nth(n);
            let actual = iter.nth(n);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_iter_nth_1() {
        let set = BitSetArray::<1>::from_fn(|x| x == 63);
        let expected_set = Vec::from_iter((0..64usize).filter(|x| *x == 63));

        let mut iter = set.into_iter();
        let mut expected_iter = expected_set.into_iter();

        for n in [0, 1] {
            let expected = expected_iter.nth(n);
            let actual = iter.nth(n);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_iter_nth_back_4() {
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0);
        let expected_set = Vec::from_iter((0..256usize).filter(|x| x % 7 == 0));

        let mut iter = set.into_iter();
        let mut expected_iter = expected_set.into_iter();

        for n in [0, 1, 10, 2, 3, 0, 0, 2, 3] {
            let expected = expected_iter.nth_back(n);
            let actual = iter.nth_back(n);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_iter_fold4() {
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0);
        let iter = set.into_iter();
        let fold_result = iter.fold(13, |acc, x| acc + x);

        assert_eq!(fold_result, 4675);

        let complete_set = BitSetArray::<4>::ALL;

        assert_eq!(
            complete_set.into_iter().fold(Vec::new(), |mut vec, v| {
                vec.push(v);
                vec
            }),
            Vec::from_iter(0..256)
        );
    }

    #[test]
    fn test_iter_rfold4() {
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0);
        let iter = set.into_iter();
        let fold_result = iter.rfold(13, |acc, x| acc + x);

        assert_eq!(fold_result, 4675);

        let complete_set = BitSetArray::<4>::ALL;

        assert_eq!(
            complete_set.into_iter().rfold(Vec::new(), |mut vec, v| {
                vec.push(v);
                vec
            }),
            Vec::from_iter((0..256).rev())
        );
    }

    #[test]
    fn test_sum() {
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0 || x % 4 == 0);
        let expected_set = Vec::from_iter((0..256usize).filter(|x| x % 7 == 0 || x % 4 == 0));

        let sum: usize = set.into_iter().sum();
        let expected_sum: usize = expected_set.into_iter().sum();

        assert_eq!(sum, expected_sum);

        assert_eq!(
            BitSetArray::<4>::ALL.into_iter().sum::<usize>(),
            (0..256).sum()
        );
    }

    #[test]
    pub fn from_fn_1() {
        let evens = BitSetArray::<1>::from_fn(|x| x % 2 == 0);

        assert_eq!(32, evens.count());
        let iter = evens.into_iter();
        assert_eq!(iter.len(), 32);

        let items: Vec<usize> = iter.collect();
        let expected: Vec<usize> = (0..32usize).map(|x| x * 2).collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn from_iter_1() {
        let expected: Vec<usize> = (0..13usize).map(|x| x * 5).collect();

        let set = BitSetArray::<1>::from_iter(expected.iter().copied());

        assert_eq!(13, set.count());

        let iter = set.into_iter();
        assert_eq!(iter.len(), 13);
        assert_eq!(iter.size_hint(), (13, Some(13)));

        let items: Vec<usize> = iter.collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn reverse_iter_1() {
        let expected: Vec<usize> = (0..13usize).map(|x| x * 5).rev().collect();

        let set = BitSetArray::<1>::from_iter(expected.iter().copied());

        assert_eq!(13, set.count());

        let iter = set.into_iter();
        assert_eq!(iter.len(), 13);
        assert_eq!(iter.size_hint(), (13, Some(13)));

        let items: Vec<usize> = iter.rev().collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn is_empty_1() {
        let mut my_set = BitSetArray::<1>::EMPTY;

        assert!(my_set.is_empty());

        my_set.set_bit(63, true);

        assert!(!my_set.is_empty());

        my_set.set_bit(63, false);

        assert!(my_set.is_empty());
    }

    #[test]
    pub fn from_inner_1() {
        let evens = BitSetArray::<1>::from_fn(|x| x % 2 == 0);
        let inner = evens.into_inner();

        assert_eq!(inner, [6_148_914_691_236_517_205; 1]);
        let again = BitSetArray::from_inner(inner);

        assert_eq!(evens, again);

        let eq = evens.eq(&again);

        assert!(eq);
    }

    #[test]
    pub fn contains_1() {
        let my_set = BitSetArray::<1>::from_fn(|x| x % 2 == 0);

        for x in 0..70 {
            let value = my_set.contains(x);

            assert_eq!(x % 2 == 0 && x < 64, value);
        }
    }

    #[test]
    pub fn set_bit_1() {
        let mut my_set = BitSetArray::<1>::from_fn(|x| x % 2 == 0);
        my_set.set_bit(1, true);
        my_set.set_bit(33, true);

        my_set.set_bit(2, false);
        my_set.set_bit(32, false);

        let mut expected: BTreeSet<usize> = (0..32usize).map(|x| x * 2).collect();
        expected.insert(1);
        expected.insert(33);
        expected.remove(&2);
        expected.remove(&32);

        let actual: Vec<_> = my_set.into_iter().collect();
        let expected: Vec<_> = expected.into_iter().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    pub fn with_bit_set_1() {
        let my_set = BitSetArray::<1>::from_fn(|x| x % 2 == 0)
            .with_bit_set(1, true)
            .with_bit_set(33, true)
            .with_bit_set(2, false)
            .with_bit_set(32, false);

        let mut expected: BTreeSet<usize> = (0..32usize).map(|x| x * 2).collect();
        expected.insert(1);
        expected.insert(33);
        expected.remove(&2);
        expected.remove(&32);

        let actual: Vec<_> = my_set.into_iter().collect();
        let expected: Vec<_> = expected.into_iter().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    pub fn union_1() {
        let multiples_of_2 = BitSetArray::<1>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSetArray::<1>::from_fn(|x| x % 5 == 0);
        let multiples_of_2_or_5 = BitSetArray::<1>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let union = multiples_of_2.union(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5, union);
    }

    #[test]
    pub fn intersect_1() {
        let multiples_of_2 = BitSetArray::<1>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSetArray::<1>::from_fn(|x| x % 5 == 0);
        let multiples_of_10 = BitSetArray::<1>::from_fn(|x| x % 10 == 0);
        let multiples_of_6 = BitSetArray::<1>::from_fn(|x| x % 6 == 0);

        let intersection = multiples_of_2.intersect(&multiples_of_5);

        assert_eq!(multiples_of_10, intersection);

        assert!(intersection.is_subset(&multiples_of_2));
        assert!(intersection.is_subset(&multiples_of_5));
        assert!(intersection.is_subset(&multiples_of_10));

        assert!(!intersection.is_superset(&multiples_of_2));
        assert!(!intersection.is_superset(&multiples_of_5));
        assert!(intersection.is_superset(&multiples_of_10));

        assert!(!multiples_of_2.is_subset(&intersection));
        assert!(!multiples_of_5.is_subset(&intersection));
        assert!(intersection.is_subset(&intersection));

        assert!(multiples_of_2.is_superset(&intersection));
        assert!(multiples_of_5.is_superset(&intersection));
        assert!(intersection.is_superset(&intersection));

        assert!(!intersection.is_subset(&multiples_of_6));
        assert!(!intersection.is_superset(&multiples_of_6));
    }

    #[test]
    pub fn symmetric_difference_1() {
        let multiples_of_2 = BitSetArray::<1>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSetArray::<1>::from_fn(|x| x % 5 == 0);

        let multiples_of_2_or_5_but_not_10 =
            BitSetArray::<1>::from_fn(|x| x % 10 != 0 && (x % 2 == 0 || x % 5 == 0));

        let sym_diff = multiples_of_2.symmetric_difference(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5_but_not_10, sym_diff);
    }

    #[test]
    pub fn negate_1() {
        let evens = BitSetArray::<1>::from_fn(|x| x % 2 == 0);
        let odds = BitSetArray::<1>::from_fn(|x| x % 2 == 1);

        let negated_evens = evens.negate();

        assert_eq!(negated_evens, odds);
    }

    #[test]
    fn test_serde_empty_1() {
        use serde_test::*;
        let map = BitSetArray::<1>::EMPTY;

        assert_tokens(
            &map,
            &[
                Token::NewtypeStruct {
                    name: "BitSetArray",
                },
                Token::Tuple { len: 1 },
                Token::U64(0),
                Token::TupleEnd,
            ],
        );
    }

    #[test]
    fn test_serde_1() {
        use serde_test::*;
        let map = BitSetArray::<1>::from_fn(|x| x % 2 == 0);

        assert_tokens(
            &map,
            &[
                Token::NewtypeStruct {
                    name: "BitSetArray",
                },
                Token::Tuple { len: 1 },
                Token::U64(6_148_914_691_236_517_205),
                Token::TupleEnd,
            ],
        );
    }

    #[test]
    fn test_first1() {
        let mut set = BitSetArray::<1>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..64).filter(|x| x % 2 == 0 || x % 5 == 0).collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(first) = set.first() {
            set.set_bit(first, false);
            actual.push(first);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_last1() {
        let mut set = BitSetArray::<1>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..64).filter(|x| x % 2 == 0 || x % 5 == 0).rev().collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(last) = set.last() {
            set.set_bit(last, false);
            actual.push(last);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_pop_1() {
        let mut set = BitSetArray::<1>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..64).filter(|x| x % 2 == 0 || x % 5 == 0).collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(first) = set.pop() {
            actual.push(first);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_pop_last1() {
        let mut set = BitSetArray::<1>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..64).filter(|x| x % 2 == 0 || x % 5 == 0).rev().collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(last) = set.pop_last() {
            actual.push(last);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_display() {
        let mut set = BitSetArray::<2>::from_iter([0, 1, 99]);

        set.remove(1);
        set.insert(100);

        assert_eq!(set.to_string(), "[0, 99, 100]");
    }

    #[test]
    fn test_iter_subsets() {
        let set = BitSetArray::<1>::from_iter([0, 1, 2, 3, 4]);

        for size in 0u32..=5 {
            let iter = set.iter_subsets(size);
            let expected_len = n_choose_k(set.count(), size);
            assert_eq!(iter.len(), expected_len as usize);
            let results: Vec<_> = iter.collect();

            assert_eq!(results.len(), expected_len as usize);

            for r in &results {
                assert_eq!(r.count(), size, "Result should have the correct size");
                assert!(r.is_subset(&set), "Result should be a subset of the set");
            }

            let mut sorted_results = results.clone();
            sorted_results.sort();
            sorted_results.dedup();

            assert_eq!(
                results, sorted_results,
                "Results should be sorted and free of duplicates"
            );
        }
    }
}
