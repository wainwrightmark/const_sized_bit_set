#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![allow(warnings, dead_code, unused_imports, unused_mut)]
#![warn(clippy::pedantic)]
mod n_choose_k;

use core::{iter::FusedIterator, ops::Shr};
use n_choose_k::n_choose_k;
#[cfg(any(test, feature = "serde"))]
use serde::{Deserialize, Serialize};
use core::fmt::{Debug, Write};

/// A set whose members are unsigned integers in `0..(64 * WORDS)`
/// Most operations are O(1)
///
/// Set `b` is considered greater than set `a` if the largest element that is contained in `a | b` but not `a & b` is in `b`.
/// Therefore sets are ordered like [], [0], [1], [0,1], [2], [0,2], [1,2], [0,1,2]
#[must_use]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(any(test, feature = "serde"), derive(Serialize, Deserialize))]
pub struct BitSet<const WORDS: usize>(
    #[cfg_attr(any(test, feature = "serde"), serde(with = "serde_arrays"))] [u64; WORDS],
);

impl<const WORDS: usize> core::fmt::Display for BitSet<WORDS> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_char('[');
        let mut write_commas: bool = false;
        for x in self.into_iter() {
            if write_commas {
                f.write_char(',');
                f.write_char(' ');
            } else {
                write_commas = true;
            }
            core::fmt::Display::fmt(&x, f);
        }

        f.write_char(']');
        Ok(())
    }
}

impl<const WORDS: usize> Default for BitSet<WORDS> {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl<const WORDS: usize> BitSet<WORDS> {
    /// The set where all tiles are missing
    pub const EMPTY: Self = { Self([0; WORDS]) };

    /// The set where all tiles are present
    pub const ALL: Self = { Self::EMPTY.negate() };

    #[inline]
    #[must_use]
    pub fn from_fn<F: FnMut(usize) -> bool>(mut cb: F) -> Self {
        let mut result = Self::default();
        for x in 0..(WORDS * (u64::BITS as usize)) {
            if cb(x) {
                result.set_bit(x, true);
            }
        }

        result
    }

    #[inline]
    pub fn from_iter(iter: impl Iterator<Item = usize>) -> Self {
        let mut r = Self::default();
        for x in iter {
            r.set_bit(x, true);
        }
        r
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
        return true;
    }

    #[must_use]
    #[inline]
    pub const fn is_empty(self) -> bool {
        self.eq(&Self::EMPTY)
    }

    /// Sets the bit at `index` to `bit`
    /// PANICS if index is out of range
    #[inline]
    pub fn set_bit(&mut self, index: usize, bit: bool) {
        let word = index / u64::BITS as usize;
        let shift = (index % u64::BITS as usize) as u32;

        if bit {
            //todo remove branch?
            self.0[word] |= 1u64 << shift;
        } else {
            self.0[word] &= !(1u64 << shift);
        }
    }

    /// Returns a copy of `self` with the bit at `index` set to `bit`
    /// PANICS if index is out of range
    #[must_use]
    #[inline]
    pub const fn with_bit_set(&self, index: usize, bit: bool) -> Self {
        let word = index / u64::BITS as usize;
        let shift = (index % u64::BITS as usize) as u32;

        let inner = if bit {
            //todo remove branch?
            self.0[word] | (1u64 << shift)
        } else {
            self.0[word] & !(1u64 << shift)
        };

        let mut arr = self.0;
        arr[word] = inner;

        Self(arr)
    }

    #[must_use]
    #[inline]
    pub const fn get_bit(&self, index: usize) -> bool {
        let word_index = index / u64::BITS as usize;
        let shift = (index % u64::BITS as usize) as u32;

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

    /// The first element in this set
    #[must_use]
    #[inline]
    pub const fn first(&self) -> Option<usize> {
        let mut word = 0;
        while word < WORDS {
            let tz = self.0[word].trailing_zeros();
            if tz < u64::BITS {
                return Some(tz as usize + (word * (u64::BITS as usize)));
            }
            word += 1;
        }
        None
    }

    /// The last element in this set
    #[must_use]
    #[inline]
    pub const fn last(&self) -> Option<usize> {
        let mut word = WORDS;

        while let Some(nw) = word.checked_sub(1) {
            word = nw;

            if let Some(index) = (u64::BITS - 1).checked_sub(self.0[word].leading_zeros()) {
                return Some(index as usize + (word * (u64::BITS as usize)));
            }
        }
        return None;
    }

    /// The removes the first (smallest) element of the set and returns it
    /// Returns `None` if the set is empty
    #[must_use]
    #[inline]
    pub fn pop(&mut self) -> Option<usize> {
        let mut word = 0;
        while word < WORDS {
            let tz = self.0[word].trailing_zeros();
            if tz < u64::BITS {
                let r = tz as usize + (word * (u64::BITS as usize));
                self.0[word] &= !(1u64 << tz);

                return Some(r);
            }
            word += 1;
        }
        None
    }

    /// The last element in this set
    #[must_use]
    #[inline]
    pub fn pop_last(&mut self) -> Option<usize> {
        let mut word = WORDS;

        while let Some(nw) = word.checked_sub(1) {
            word = nw;

            if let Some(index) = (u64::BITS - 1).checked_sub(self.0[word].leading_zeros()) {
                let r = index as usize + (word * (u64::BITS as usize));
                self.0[word] &= !(1u64 << index);
                return Some(r);
            }
        }
        return None;
    }

    fn subset_index_to_members(&self, subset_size: u32, index: u32, member_count: u32) -> Self {
        let mut n_c_k = crate::n_choose_k::NChooseK::new(self.count(), subset_size, member_count);

        // essentially reverse the order
        let mut index = n_c_k.result() - (index + 1);
        let mut index = index;
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

        let mut set_remaining = self.clone();

        while let Some(next) = set_remaining.pop_last() {
            //let number_containing = n_choose_k(remaining_count - 1, remaining_needed - 1);
            match index.checked_sub(n_c_k.result()) {
                Some(new_index) => {
                    index = new_index;
                }
                None => {
                    new_set.set_bit(next, true);
                    match n_c_k.try_decrement_k() {
                        Some(r) => n_c_k = r,
                        None => return new_set,
                    }
                }
            }
            match n_c_k.try_decrement_n() {
                Some(r) => n_c_k = r,
                None => return new_set.union(&set_remaining),
            }
        }

        return new_set;
    }

    pub fn iter_subsets(
        &self,
        subset_size: u32,
    ) -> impl Iterator<Item = Self>
           + FusedIterator
           + DoubleEndedIterator
           + ExactSizeIterator
           + Debug
           + Clone
           + PartialEq
           + 'static {
        let member_count = n_choose_k(self.count(), subset_size);
        BitSetSubsetIter::<WORDS> {
            set: self.clone(),
            subset_size,
            member_count,
            next_index: 0,
            after_last_index: member_count,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct BitSetSubsetIter<const WORDS: usize> {
    set: BitSet<WORDS>,
    subset_size: u32,
    member_count: u32,
    next_index: u32,
    after_last_index: u32,
}

impl<const WORDS: usize> ExactSizeIterator for BitSetSubsetIter<WORDS> {
    fn len(&self) -> usize {
        let (lower, upper) = self.size_hint();
        // Note: This assertion is overly defensive, but it checks the invariant
        // guaranteed by the trait. If this trait were rust-internal,
        // we could use debug_assert!; assert_eq! will check all Rust user
        // implementations too.
        debug_assert_eq!(upper, Some(lower));
        lower
    }
}

impl<const WORDS: usize> DoubleEndedIterator for BitSetSubsetIter<WORDS> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.next_index >= self.after_last_index {
            return None;
        }
        self.after_last_index -= 1;
        let r = self.set.subset_index_to_members(
            self.subset_size,
            self.after_last_index,
            self.member_count,
        );

        Some(r)
    }
}

impl<const WORDS: usize> FusedIterator for BitSetSubsetIter<WORDS> {}

impl<const WORDS: usize> Iterator for BitSetSubsetIter<WORDS> {
    type Item = BitSet<WORDS>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next_index >= self.after_last_index {
            return None;
        }
        let r =
            self.set
                .subset_index_to_members(self.subset_size, self.next_index, self.member_count);
        self.next_index += 1;
        Some(r)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let c = self.after_last_index.saturating_sub(self.next_index) as usize;
        (c, Some(c))
    }
}

struct IterSubsetsState<const WORDS: usize> {
    remaining: BitSet<WORDS>,
    fixed: BitSet<WORDS>,
}

impl<const WORDS: usize> core::fmt::Display for IterSubsetsState<WORDS> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{{{} {}}}", self.remaining, self.fixed)
    }
}

impl<const WORDS: usize> IntoIterator for BitSet<WORDS> {
    type Item = usize;

    type IntoIter = BitSetIter<WORDS>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        BitSetIter { inner: self }
    }
}

#[must_use]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitSetIter<const WORDS: usize> {
    //TODO use more efficient iterator if size is greater than one
    inner: BitSet<WORDS>,
}

impl<const WORDS: usize> ExactSizeIterator for BitSetIter<WORDS> {}
impl<const WORDS: usize> FusedIterator for BitSetIter<WORDS> {}

impl<const WORDS: usize> Iterator for BitSetIter<WORDS> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.pop()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let c = self.count();
        (c, Some(c))
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.inner.count() as usize
    }
}

impl<const WORDS: usize> DoubleEndedIterator for BitSetIter<WORDS> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.pop_last()
    }
}

#[cfg(test)]
pub mod tests {
    use std::collections::BTreeSet;

    use crate::n_choose_k::*;
    use crate::BitSet;

    #[test]
    pub fn from_fn_4() {
        let evens = BitSet::<4>::from_fn(|x| x % 2 == 0);

        assert_eq!(128, evens.count());
        let iter = evens.into_iter();
        assert_eq!(iter.count(), 128);

        let items: Vec<usize> = iter.collect();
        let expected: Vec<usize> = (0..128usize).map(|x| x * 2).collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn from_iter_4() {
        let expected: Vec<usize> = (0..52usize).map(|x| x * 5).collect();

        let set = BitSet::<4>::from_iter(expected.iter().cloned());

        assert_eq!(52, set.count());

        let iter = set.into_iter();
        assert_eq!(iter.count(), 52);
        assert_eq!(iter.size_hint(), (52, Some(52)));

        let items: Vec<usize> = iter.collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn reverse_iter_4() {
        let expected: Vec<usize> = (0..52usize).map(|x| x * 5).rev().collect();

        let set = BitSet::<4>::from_iter(expected.iter().cloned());

        assert_eq!(52, set.count());

        let iter = set.into_iter();
        assert_eq!(iter.count(), 52);
        assert_eq!(iter.size_hint(), (52, Some(52)));

        let items: Vec<usize> = iter.rev().collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn is_empty_4() {
        let mut my_set = BitSet::<4>::EMPTY;

        assert!(my_set.is_empty());

        my_set.set_bit(255, true);

        assert!(!my_set.is_empty());

        my_set.set_bit(255, false);

        assert!(my_set.is_empty());
    }

    #[test]
    pub fn from_inner_4() {
        let evens = BitSet::<4>::from_fn(|x| x % 2 == 0);
        let inner = evens.into_inner();

        assert_eq!(inner, [6148914691236517205; 4]);
        let again = BitSet::from_inner(inner);

        assert_eq!(evens, again);

        let eq = evens.eq(&again);

        assert!(eq);
    }

    #[test]
    pub fn get_bit_4() {
        let my_set = BitSet::<4>::from_fn(|x| x % 2 == 0);

        for x in 0..260 {
            let value = my_set.get_bit(x);

            assert_eq!(x % 2 == 0 && x < 256, value);
        }
    }

    #[test]
    pub fn set_bit_4() {
        let mut my_set = BitSet::<4>::from_fn(|x| x % 2 == 0);
        my_set.set_bit(1, true);
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

        assert_eq!(actual, expected)
    }

    #[test]
    pub fn with_bit_set_4() {
        let my_set = BitSet::<4>::from_fn(|x| x % 2 == 0)
            .with_bit_set(1, true)
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

        assert_eq!(actual, expected)
    }

    #[test]
    pub fn union_4() {
        let multiples_of_2 = BitSet::<4>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSet::<4>::from_fn(|x| x % 5 == 0);
        let multiples_of_2_or_5 = BitSet::<4>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let union = multiples_of_2.union(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5, union);
    }

    #[test]
    pub fn intersect_4() {
        let multiples_of_2 = BitSet::<4>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSet::<4>::from_fn(|x| x % 5 == 0);
        let multiples_of_10 = BitSet::<4>::from_fn(|x| x % 10 == 0);
        let multiples_of_6 = BitSet::<4>::from_fn(|x| x % 6 == 0);

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
        let multiples_of_2 = BitSet::<4>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSet::<4>::from_fn(|x| x % 5 == 0);

        let multiples_of_2_or_5_but_not_10 =
            BitSet::<4>::from_fn(|x| x % 10 != 0 && (x % 2 == 0 || x % 5 == 0));

        let sym_diff = multiples_of_2.symmetric_difference(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5_but_not_10, sym_diff);
    }

    #[test]
    pub fn negate_4() {
        let evens = BitSet::<4>::from_fn(|x| x % 2 == 0);
        let odds = BitSet::<4>::from_fn(|x| x % 2 == 1);

        let negated_evens = evens.negate();

        assert_eq!(negated_evens, odds);
    }

    #[test]
    fn test_serde_empty_4() {
        use serde_test::*;
        let map = BitSet::<4>::EMPTY;

        assert_tokens(
            &map,
            &[
                Token::NewtypeStruct { name: "BitSet" },
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
        let map = BitSet::<4>::from_fn(|x| x % 2 == ((x / 64) % 2));

        assert_tokens(
            &map,
            &[
                Token::NewtypeStruct { name: "BitSet" },
                Token::Tuple { len: 4 },
                Token::U64(6148914691236517205),
                Token::U64(12297829382473034410),
                Token::U64(6148914691236517205),
                Token::U64(12297829382473034410),
                Token::TupleEnd,
            ],
        );
    }

    #[test]
    fn test_first4() {
        let mut set = BitSet::<4>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..256)
            .into_iter()
            .filter(|x| x % 2 == 0 || x % 5 == 0)
            .collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(first) = set.first() {
            set.set_bit(first, false);
            actual.push(first);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_last4() {
        let mut set = BitSet::<4>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..256)
            .into_iter()
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
        let mut set = BitSet::<4>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..256)
            .into_iter()
            .filter(|x| x % 2 == 0 || x % 5 == 0)
            .collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(first) = set.pop() {
            actual.push(first);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_pop_last4() {
        let mut set = BitSet::<4>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..256)
            .into_iter()
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
    pub fn from_fn_1() {
        let evens = BitSet::<1>::from_fn(|x| x % 2 == 0);

        assert_eq!(32, evens.count());
        let iter = evens.into_iter();
        assert_eq!(iter.count(), 32);

        let items: Vec<usize> = iter.collect();
        let expected: Vec<usize> = (0..32usize).map(|x| x * 2).collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn from_iter_1() {
        let expected: Vec<usize> = (0..13usize).map(|x| x * 5).collect();

        let set = BitSet::<1>::from_iter(expected.iter().cloned());

        assert_eq!(13, set.count());

        let iter = set.into_iter();
        assert_eq!(iter.count(), 13);
        assert_eq!(iter.size_hint(), (13, Some(13)));

        let items: Vec<usize> = iter.collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn reverse_iter_1() {
        let expected: Vec<usize> = (0..13usize).map(|x| x * 5).rev().collect();

        let set = BitSet::<1>::from_iter(expected.iter().cloned());

        assert_eq!(13, set.count());

        let iter = set.into_iter();
        assert_eq!(iter.count(), 13);
        assert_eq!(iter.size_hint(), (13, Some(13)));

        let items: Vec<usize> = iter.rev().collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn is_empty_1() {
        let mut my_set = BitSet::<1>::EMPTY;

        assert!(my_set.is_empty());

        my_set.set_bit(63, true);

        assert!(!my_set.is_empty());

        my_set.set_bit(63, false);

        assert!(my_set.is_empty());
    }

    #[test]
    pub fn from_inner_1() {
        let evens = BitSet::<1>::from_fn(|x| x % 2 == 0);
        let inner = evens.into_inner();

        assert_eq!(inner, [6148914691236517205; 1]);
        let again = BitSet::from_inner(inner);

        assert_eq!(evens, again);

        let eq = evens.eq(&again);

        assert!(eq);
    }

    #[test]
    pub fn get_bit_1() {
        let my_set = BitSet::<1>::from_fn(|x| x % 2 == 0);

        for x in 0..70 {
            let value = my_set.get_bit(x);

            assert_eq!(x % 2 == 0 && x < 64, value);
        }
    }

    #[test]
    pub fn set_bit_1() {
        let mut my_set = BitSet::<1>::from_fn(|x| x % 2 == 0);
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

        assert_eq!(actual, expected)
    }

    #[test]
    pub fn with_bit_set_1() {
        let my_set = BitSet::<1>::from_fn(|x| x % 2 == 0)
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

        assert_eq!(actual, expected)
    }

    #[test]
    pub fn union_1() {
        let multiples_of_2 = BitSet::<1>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSet::<1>::from_fn(|x| x % 5 == 0);
        let multiples_of_2_or_5 = BitSet::<1>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let union = multiples_of_2.union(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5, union);
    }

    #[test]
    pub fn intersect_1() {
        let multiples_of_2 = BitSet::<1>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSet::<1>::from_fn(|x| x % 5 == 0);
        let multiples_of_10 = BitSet::<1>::from_fn(|x| x % 10 == 0);
        let multiples_of_6 = BitSet::<1>::from_fn(|x| x % 6 == 0);

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
        let multiples_of_2 = BitSet::<1>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSet::<1>::from_fn(|x| x % 5 == 0);

        let multiples_of_2_or_5_but_not_10 =
            BitSet::<1>::from_fn(|x| x % 10 != 0 && (x % 2 == 0 || x % 5 == 0));

        let sym_diff = multiples_of_2.symmetric_difference(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5_but_not_10, sym_diff);
    }

    #[test]
    pub fn negate_1() {
        let evens = BitSet::<1>::from_fn(|x| x % 2 == 0);
        let odds = BitSet::<1>::from_fn(|x| x % 2 == 1);

        let negated_evens = evens.negate();

        assert_eq!(negated_evens, odds);
    }

    #[test]
    fn test_serde_empty_1() {
        use serde_test::*;
        let map = BitSet::<1>::EMPTY;

        assert_tokens(
            &map,
            &[
                Token::NewtypeStruct { name: "BitSet" },
                Token::Tuple { len: 1 },
                Token::U64(0),
                Token::TupleEnd,
            ],
        );
    }

    #[test]
    fn test_serde_1() {
        use serde_test::*;
        let map = BitSet::<1>::from_fn(|x| x % 2 == 0);

        assert_tokens(
            &map,
            &[
                Token::NewtypeStruct { name: "BitSet" },
                Token::Tuple { len: 1 },
                Token::U64(6148914691236517205),
                Token::TupleEnd,
            ],
        );
    }

    #[test]
    fn test_first1() {
        let mut set = BitSet::<1>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..64)
            .into_iter()
            .filter(|x| x % 2 == 0 || x % 5 == 0)
            .collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(first) = set.first() {
            set.set_bit(first, false);
            actual.push(first);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_last1() {
        let mut set = BitSet::<1>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..64)
            .into_iter()
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
    fn test_pop_1() {
        let mut set = BitSet::<1>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..64)
            .into_iter()
            .filter(|x| x % 2 == 0 || x % 5 == 0)
            .collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(first) = set.pop() {
            actual.push(first);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_pop_last1() {
        let mut set = BitSet::<1>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..64)
            .into_iter()
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
    fn test_display() {
        let set = BitSet::<1>::from_iter([1, 2, 3, 4, 5].into_iter());

        assert_eq!(set.to_string(), "[1, 2, 3, 4, 5]");
    }

    #[test]
    fn test_iter_subsets() {
        let set = BitSet::<1>::from_iter([0, 1, 2, 3, 4].into_iter());

        for size in 0u32..=5 {

            let iter = set.iter_subsets(size as u32);
            let expected_len = n_choose_k(set.count(), size);
            assert_eq!(iter.len(), expected_len as usize);
            let results: Vec<_> = iter.collect();
            
            assert_eq!(results.len(), expected_len as usize);

            for r in results.iter() {
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
            // for r in results {
            //     println!("{r}");
            // }
            // println!("")
        }
    }

    // #[test]
    // pub fn index_to_members() {
    //     let set = BitSet::<1>::from_iter([0, 1, 2, 3, 4].into_iter());

    //     for x in 0..10u32 {
    //         let subset = set.subset_index_to_members(3, x, n_choose_k(5, 3));

    //         println!("{subset}");
    //     }
    // }
}
