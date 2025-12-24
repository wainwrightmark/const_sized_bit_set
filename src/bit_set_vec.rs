use crate::prelude::BitSet;
use crate::slice_iter::SliceIter;
use crate::{BitSet64, SetElement};
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(any(test, feature = "serde"), derive(Serialize, Deserialize))]
pub struct BitSetVec(Vec<u64>);
//todo enforce that the inner vector never has extra zeros at the end

impl core::fmt::Display for BitSetVec {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_char('[')?;
        let mut write_commas: bool = false;
        for x in self.iter() {
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

impl Default for BitSetVec {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl BitSetVec {
    #[inline]
    #[must_use]
    pub fn from_fn<F: FnMut(u32) -> bool>(max_elements: u32, mut cb: F) -> Self {
        let mut result = Self::default();
        for x in (0..max_elements).filter(|x| cb(*x)) {
            result.insert(x);
        }

        result
    }

    #[inline]
    #[must_use]
    fn enumerate_sets(
        &self,
    ) -> impl ExactSizeIterator<Item = (usize, BitSet64)> + DoubleEndedIterator + use<'_> {
        self.0
            .iter()
            .map(|x| BitSet64::from_inner_const(*x))
            .enumerate()
    }
    #[inline]
    fn get_or_create_word_n(&mut self, word_index: usize) -> &mut u64 {
        if let Some(diff) = (word_index + 1).checked_sub(self.0.len()) {
            self.0.extend(std::iter::repeat_n(0, diff));
        }
        self.0.get_mut(word_index).unwrap()
    }

    #[inline]
    #[must_use]
    fn try_get_word_set(&self, word: usize) -> Option<BitSet64> {
        self.0.get(word).map(|&x| BitSet64::from_inner_const(x))
    }

    #[inline]
    #[must_use]
    fn to_word_and_shift(element: SetElement) -> (usize, SetElement) {
        let word_index = (element / WORD_BITS) as usize;
        let shift = element % WORD_BITS;
        (word_index, shift)
    }

    #[inline]
    #[must_use]
    #[expect(clippy::cast_possible_truncation)]
    fn to_full_set_element(element: SetElement, word_index: usize) -> SetElement {
        element + (word_index as u32 * WORD_BITS)
    }

    
}

const WORD_BITS: u32 = u64::BITS;

impl BitSet for BitSetVec {
    type Inner = Vec<u64>;

    const EMPTY: Self = Self(vec![]);

    fn is_empty(&self) -> bool {
        self.0.iter().all(|x| *x == 0)
    }

    fn count(&self) -> u32 {
        self.0.iter().map(|x| x.count_ones()).sum()
    }

    fn clear(&mut self) {
        self.0.clear();
    }

    fn into_inner(self) -> Self::Inner {
        self.0
    }

    fn from_inner(inner: Self::Inner) -> Self {
        Self(inner)
    }

    fn from_first_n(n: u32) -> Self {
        let (full_words, extra_elements) = Self::to_word_and_shift(n);
        let mut inner = Vec::with_capacity(full_words + if extra_elements == 0 { 0 } else { 1 });
        let mut i = 0;
        while i < full_words {
            inner.push(u64::MAX);
            i += 1;
        }
        if extra_elements > 0 {
            inner.push(BitSet64::from_first_n(extra_elements).into_inner_const());
        }

        Self(inner)
    }

    fn contains(&self, element: SetElement) -> bool {
        let (word_index, shift) = Self::to_word_and_shift(element);
        self.try_get_word_set(word_index)
            .is_some_and(|x| x.contains_const(shift))
    }

    fn first(&self) -> Option<SetElement> {
        self.enumerate_sets()
            .filter_map(|(word_index, set)| {
                set.first_const()
                    .map(|x| Self::to_full_set_element(x, word_index))
            })
            .next()
    }

    fn last(&self) -> Option<SetElement> {
        self.enumerate_sets()
            .rev()
            .filter_map(|(word_index, set)| {
                set.last_const()
                    .map(|x| Self::to_full_set_element(x, word_index))
            })
            .next()
    }

    fn pop(&mut self) -> Option<SetElement> {
        for (word_index, inner) in self.0.iter_mut().enumerate() {
            if let Some(e) = crate::mutate_inner(inner, super::bit_set_n::BitSet64::pop_const) {
                return Some(Self::to_full_set_element(e, word_index));
            }
        }
        None
    }

    fn pop_last(&mut self) -> Option<SetElement> {
        for (word_index, inner) in self.0.iter_mut().enumerate().rev() {
            if let Some(e) = crate::mutate_inner(inner, super::bit_set_n::BitSet64::pop_last_const) {
                return Some(Self::to_full_set_element(e, word_index));
            }
        }
        None
    }

    fn iter<'a>(
        &'a self,
    ) -> impl Iterator<Item = SetElement> + Clone + FusedIterator + DoubleEndedIterator + ExactSizeIterator
    {
        SliceIter::new(&self.0)
    }

    fn insert(&mut self, element: SetElement) -> bool {
        let (word_index, shift) = Self::to_word_and_shift(element);
        let word = self.get_or_create_word_n(word_index);
        crate::mutate_inner(word, |s| s.insert_const(shift))
    }

    fn remove(&mut self, element: SetElement) -> bool {
        let (word_index, shift) = Self::to_word_and_shift(element);
        match self.0.get_mut(word_index) {
            Some(inner) => crate::mutate_inner(inner, |s| s.remove_const(shift)),
            None => false,
        }
    }

    fn swap_bits(&mut self, i: u32, j: u32) {
        //todo improve performance???
        let i_bit = self.contains(i);
        let j_bit = self.contains(j);
        self.set_bit(i, j_bit);
        self.set_bit(j, i_bit);
    }

    fn is_subset(&self, rhs: &Self) -> bool {
        for (word_index, set) in self.enumerate_sets().rev() {
            if set.is_empty() {
                continue;
            };

            match rhs.try_get_word_set(word_index) {
                Some(rhs_set) => {
                    if !set.is_subset_const(&rhs_set) {
                        return false;
                    }
                }
                None => return false,
            }
        }
        true
    }

    fn overlaps(&self, rhs: &Self) -> bool {
        for index in 0..(self.0.len().min(rhs.0.len())) {
            let s = self.try_get_word_set(index).unwrap();
            let r = rhs.try_get_word_set(index).unwrap();
            if s.overlaps_const(&r) {
                return true;
            }
        }
        false
    }

    fn intersect_with(&mut self, rhs: &Self) {
        for (word_index, s_inner) in self.0.iter_mut().enumerate() {
            match rhs.try_get_word_set(word_index) {
                Some(r_set) => crate::mutate_inner(s_inner, |s| s.intersect_with(&r_set)),
                None => *s_inner = 0,
            }
        }
    }

    fn union_with(&mut self, rhs: &Self) {
        for (word_index, r_set) in rhs.enumerate_sets() {
            let s_inner = self.get_or_create_word_n(word_index);
            crate::mutate_inner(s_inner, |s| s.union_with_const(&r_set));
        }
    }

    fn except_with(&mut self, rhs: &Self) {
        for (word_index, s_inner) in self.0.iter_mut().enumerate() {
            if let Some(r_set) = rhs.try_get_word_set(word_index) {
                crate::mutate_inner(s_inner, |s| s.except_with_const(&r_set));
            } else {
                //rhs is empty here so do nothing
            }
        }
    }

    fn symmetric_difference_with(&mut self, rhs: &Self) {
        for (word_index, r_set) in rhs.enumerate_sets() {
            let s_inner = self.get_or_create_word_n(word_index);
            *s_inner = BitSet64::from_inner_const(*s_inner)
                .with_symmetric_difference(&r_set)
                .into_inner_const();
        }
    }

    fn nth(&self, n: u32) -> Option<SetElement> {
        let mut n = n;

        for (word, set) in self.enumerate_sets() {
            if let Some(new_n) = n.checked_sub(set.count()) {
                n = new_n;
            } else {
                return set.nth_const(n).map(|e| Self::to_full_set_element(e, word));
            }
        }
        None
    }

    fn count_lesser_elements(&self, element: SetElement) -> u32 {
        let (word_index, shift) = Self::to_word_and_shift(element);
        let mut total = 0;
        for (wi, set) in self.enumerate_sets() {
            if wi == word_index {
                total += set.count_lesser_elements(shift);
                return total;
            } else {
                total += set.count();
            }
        }
        total
    }

    fn count_greater_elements(&self, element: SetElement) -> u32 {
        let (word_index, shift) = Self::to_word_and_shift(element);
        let mut total = 0;
        for (wi, set) in self.enumerate_sets().rev() {
            match wi.cmp(&word_index) {
                std::cmp::Ordering::Less => return total,
                std::cmp::Ordering::Equal => {
                    total += set.count_greater_elements(shift);
                    return total;
                }
                std::cmp::Ordering::Greater => {
                    total += set.count();
                }
            }
        }
        total
    }

    fn smallest_element_greater_than(&self, index: SetElement) -> Option<SetElement> {
        let (mut word, e) = Self::to_word_and_shift(index);

        if word >= self.0.len() {
            return None;
        }

        if let Some(x) =
            BitSet64::from_inner_const(self.0[word]).smallest_element_greater_than_const(e)
        {
            return Some(x + (word as u32 * u64::BITS));
        }
        word += 1;

        while word < self.0.len() {
            let a = BitSet64::from_inner_const(self.0[word]);
            if let Some(x) = a.first_const() {
                return Some(x + (word as u32 * u64::BITS));
            } else {
                word += 1;
            }
        }
        None
    }

    fn largest_element_less_than(&self, index: SetElement) -> Option<SetElement> {
        let (mut word, e) = Self::to_word_and_shift(index);

        if word >= self.0.len() {
            return self.last();
        }

        if let Some(x) = BitSet64::from_inner_const(self.0[word]).largest_element_less_than_const(e)
        {
            return Some(x + (word as u32 * u64::BITS));
        }

        match word.checked_sub(1) {
            Some(w) => word = w,
            None => return None,
        }

        loop {
            let a = BitSet64::from_inner_const(self.0[word]);
            if let Some(x) = a.last_const() {
                return Some(x + (word as u32 * u64::BITS));
            }

            match word.checked_sub(1) {
                Some(w) => word = w,
                None => return None,
            }
        }
    }

    fn trailing_ones(&self) -> u32 {
        let mut total = 0;
        for x in self.0.iter() {
            if *x == u64::MAX {
                total += u64::BITS;
            } else {
                total += x.trailing_ones();
                return total;
            }
        }
        return total;
    }

    fn retain<F>(&mut self,mut f: F)
    where
        F: FnMut(&SetElement) -> bool,
    {
        let mut word_index = 0;
        while let Some(word) = self.0.get_mut(word_index){
            let offset = word_index as u32 * WORD_BITS;
            for element_index  in BitSet64::from_inner_const(word.clone()).iter_const(){
                if !f(&(element_index + offset)){
                    crate::mutate_inner(word, |w|w.remove_const(element_index));
                }
            }
            word_index += 1;
        }
    }
}

impl Extend<usize> for BitSetVec {
    fn extend<T: IntoIterator<Item = usize>>(&mut self, iter: T) {
        for v in iter {
            self.insert(v as u32);
        }
    }
}

impl Extend<SetElement> for BitSetVec {
    fn extend<T: IntoIterator<Item = SetElement>>(&mut self, iter: T) {
        for v in iter {
            self.insert(v);
        }
    }
}

impl FromIterator<usize> for BitSetVec {
    #[inline]
    fn from_iter<T: IntoIterator<Item = usize>>(iter: T) -> Self {
        iter.into_iter()
            .fold(Self::default(), |acc, v| acc.with_inserted(v as u32))
    }
}

impl FromIterator<u32> for BitSetVec {
    #[inline]
    fn from_iter<T: IntoIterator<Item = u32>>(iter: T) -> Self {
        iter.into_iter()
            .fold(Self::default(), |acc, v| acc.with_inserted(v))
    }
}

#[cfg(test)]
pub mod tests {
    use crate::bit_set_trait::BitSet;
    use crate::prelude::BitSetVec;
    use std::collections::BTreeSet;

    #[test]
    pub fn from_fn_4() {
        let evens = BitSetVec::from_fn(256, |x| x % 2 == 0);

        assert_eq!(128, evens.count());
        let iter = evens.iter();
        assert_eq!(iter.len(), 128);

        let items: Vec<u32> = iter.collect();
        let expected: Vec<u32> = (0..128u32).map(|x| x * 2).collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn from_iter_4() {
        let expected: Vec<u32> = (0..52u32).map(|x| x * 5).collect();

        let set = BitSetVec::from_iter(expected.iter().copied());

        assert_eq!(52, set.count());

        let iter = set.iter();
        assert_eq!(iter.len(), 52);
        assert_eq!(iter.size_hint(), (52, Some(52)));

        let items: Vec<u32> = iter.collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn extend_4() {
        let multiples_of_5: Vec<usize> = (0..52usize).map(|x| x * 5).collect();
        let multiples_of_4: Vec<usize> = (0..64usize).map(|x| x * 4).collect();

        let mut set = BitSetVec::from_iter(multiples_of_5.iter().copied());
        set.extend(multiples_of_4);

        assert_eq!(103, set.count());

        let expected = BitSetVec::from_fn(256, |x| x % 4 == 0 || x % 5 == 0);

        assert_eq!(set, expected);
    }

    #[test]
    pub fn reverse_iter_4() {
        let expected: Vec<u32> = (0..52u32).map(|x| x * 5).rev().collect();

        let set = BitSetVec::from_iter(expected.iter().copied());

        assert_eq!(52, set.count());

        let iter = set.iter();
        assert_eq!(iter.len(), 52);
        assert_eq!(iter.size_hint(), (52, Some(52)));

        let items: Vec<u32> = iter.rev().collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn is_empty_4() {
        let mut my_set = BitSetVec::EMPTY;

        assert!(my_set.is_empty());

        my_set.set_bit(255, true);

        assert!(!my_set.is_empty());

        my_set.set_bit(255, false);

        assert!(my_set.is_empty());
    }

    #[test]
    pub fn from_inner_4() {
        let evens = BitSetVec::from_fn(256, |x| x % 2 == 0);
        let inner = evens.clone().into_inner();

        assert_eq!(inner, [6_148_914_691_236_517_205; 4]);
        let again = BitSetVec::from_inner(inner);

        assert_eq!(evens, again);

        let eq = evens.eq(&again);

        assert!(eq);
    }

    #[test]
    pub fn contains_4() {
        let my_set = BitSetVec::from_fn(256, |x| x % 2 == 0);

        for x in 0..260 {
            let value = my_set.contains(x);

            assert_eq!(x % 2 == 0 && x < 256, value);
        }
    }

    #[test]
    pub fn set_bit_4() {
        let mut my_set = BitSetVec::from_fn(256, |x| x % 2 == 0);
        my_set.set_bit(1, true);
        my_set.set_bit(1, true); //set the bit twice to test that
        my_set.set_bit(65, true);

        my_set.set_bit(2, false);
        my_set.set_bit(64, false);

        let mut expected: BTreeSet<u32> = (0..128u32).map(|x| x * 2).collect();
        expected.insert(1);
        expected.insert(65);
        expected.remove(&2);
        expected.remove(&64);

        let actual: Vec<_> = my_set.iter().collect();
        let expected: Vec<_> = expected.into_iter().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    pub fn insert_and_remove_bit_4() {
        let mut my_set = BitSetVec::from_fn(256, |x| x % 2 == 0);
        assert!(my_set.insert(1));
        assert!(!my_set.insert(1));
        assert!(my_set.insert(65));

        assert!(my_set.remove(2));
        assert!(my_set.remove(64));

        let mut expected: BTreeSet<u32> = (0..128u32).map(|x| x * 2).collect();
        expected.insert(1);
        expected.insert(65);
        expected.remove(&2);
        expected.remove(&64);

        let actual: Vec<_> = my_set.iter().collect();
        let expected: Vec<_> = expected.into_iter().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    pub fn with_bit_set_4() {
        let my_set = BitSetVec::from_fn(256, |x| x % 2 == 0)
            .with_bit_set(1, true)
            .with_bit_set(1, true) //set the bit twice to test that
            .with_bit_set(65, true)
            .with_bit_set(2, false)
            .with_bit_set(64, false);

        let mut expected: BTreeSet<u32> = (0..128u32).map(|x| x * 2).collect();
        expected.insert(1);
        expected.insert(65);
        expected.remove(&2);
        expected.remove(&64);

        let actual: Vec<_> = my_set.iter().collect();
        let expected: Vec<_> = expected.into_iter().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    pub fn union_4() {
        let multiples_of_2 = BitSetVec::from_fn(256, |x| x % 2 == 0);
        let multiples_of_5 = BitSetVec::from_fn(256, |x| x % 5 == 0);
        let multiples_of_2_or_5 = BitSetVec::from_fn(256, |x| x % 2 == 0 || x % 5 == 0);

        let union = multiples_of_2.with_union(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5, union);
    }

    #[test]
    pub fn intersect_4() {
        let multiples_of_2 = BitSetVec::from_fn(256, |x| x % 2 == 0);
        let multiples_of_5 = BitSetVec::from_fn(256, |x| x % 5 == 0);
        let multiples_of_10 = BitSetVec::from_fn(256, |x| x % 10 == 0);
        let multiples_of_6 = BitSetVec::from_fn(256, |x| x % 6 == 0);

        let intersection = multiples_of_2.with_intersect(&multiples_of_5);

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
        let multiples_of_2 = BitSetVec::from_fn(256, |x| x % 2 == 0);
        let multiples_of_5 = BitSetVec::from_fn(256, |x| x % 5 == 0);

        let multiples_of_2_or_5_but_not_10 =
            BitSetVec::from_fn(256, |x| x % 10 != 0 && (x % 2 == 0 || x % 5 == 0));

        let sym_diff = multiples_of_2.with_symmetric_difference(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5_but_not_10, sym_diff);
    }

    #[test]
    fn test_serde_empty_4() {
        use serde_test::*;
        let mut vec = BitSetVec::EMPTY;
        vec.insert(255);
        vec.remove(255);

        assert_tokens(
            &vec,
            &[
                Token::NewtypeStruct { name: "BitSetVec" },
                Token::Seq { len: Some(4) },
                Token::U64(0),
                Token::U64(0),
                Token::U64(0),
                Token::U64(0),
                Token::SeqEnd,
            ],
        );
    }

    #[test]
    fn test_serde_4() {
        use serde_test::*;
        let map = BitSetVec::from_fn(256, |x| x % 2 == ((x / 64) % 2));

        assert_tokens(
            &map,
            &[
                Token::NewtypeStruct { name: "BitSetVec" },
                Token::Seq { len: Some(4) },
                Token::U64(6_148_914_691_236_517_205),
                Token::U64(12_297_829_382_473_034_410),
                Token::U64(6_148_914_691_236_517_205),
                Token::U64(12_297_829_382_473_034_410),
                Token::SeqEnd,
            ],
        );
    }

    #[test]
    fn test_first4() {
        let mut set = BitSetVec::from_fn(256, |x| x % 2 == 0 || x % 5 == 0);

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
        let mut set = BitSetVec::from_fn(256, |x| x % 2 == 0 || x % 5 == 0);

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
        let mut set = BitSetVec::from_fn(256, |x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..256).filter(|x| x % 2 == 0 || x % 5 == 0).collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(first) = set.pop() {
            actual.push(first);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_pop_last4() {
        let mut set = BitSetVec::from_fn(256, |x| x % 2 == 0 || x % 5 == 0);

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
        let set = BitSetVec::from_fn(256, |x| x % 7 == 0);
        let iter = set.iter();
        assert_eq!(iter.last(), Some(252));
    }

    #[test]
    fn test_iter_max4() {
        let set = BitSetVec::from_fn(256, |x| x % 7 == 0 && x < 140);
        let iter = set.iter();
        let max = Iterator::max(iter);
        assert_eq!(max, Some(133));
    }

    #[test]
    fn test_iter_min4() {
        let set = BitSetVec::from_fn(256, |x| x > 64 && x % 7 == 0);
        let iter = set.iter();
        let min = Iterator::min(iter);
        assert_eq!(min, Some(70));
    }

    #[test]
    fn test_iter_nth_4() {
        let set = BitSetVec::from_fn(256, |x| x % 7 == 0);
        let expected_set = Vec::from_iter((0..256u32).filter(|x| x % 7 == 0));

        let mut iter = set.iter();
        let mut expected_iter = expected_set.into_iter();

        for n in [0, 1, 10, 2, 3, 0, 0, 2, 3] {
            let expected = expected_iter.nth(n);
            let actual = iter.nth(n);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_iter_nth_1() {
        let set = BitSetVec::from_fn(64, |x| x == 63);
        let expected_set = Vec::from_iter((0..64u32).filter(|x| *x == 63));

        let mut iter = set.iter();
        let mut expected_iter = expected_set.into_iter();

        for n in [0, 1] {
            let expected = expected_iter.nth(n);
            let actual = iter.nth(n);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_iter_nth_back_4() {
        let set = BitSetVec::from_fn(256, |x| x % 7 == 0);
        let expected_set = Vec::from_iter((0..256u32).filter(|x| x % 7 == 0));

        let mut iter = set.iter();
        let mut expected_iter = expected_set.into_iter();

        for n in [0, 1, 10, 2, 3, 0, 0, 2, 3] {
            let expected = expected_iter.nth_back(n);
            let actual = iter.nth_back(n);
            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn test_iter_fold4() {
        let set = BitSetVec::from_fn(256, |x| x % 7 == 0);
        let iter = set.iter();
        let fold_result = iter.fold(13, |acc, x| acc + x);

        assert_eq!(fold_result, 4675);

        let complete_set = BitSetVec::from_first_n(256);

        assert_eq!(
            complete_set.iter().fold(Vec::new(), |mut vec, v| {
                vec.push(v);
                vec
            }),
            Vec::from_iter(0..256)
        );
    }

    #[test]
    fn test_iter_rfold4() {
        let set = BitSetVec::from_fn(256, |x| x % 7 == 0);
        let iter = set.iter();
        let fold_result = iter.rfold(13, |acc, x| acc + x);

        assert_eq!(fold_result, 4675);

        let complete_set = BitSetVec::from_first_n(256);

        assert_eq!(
            complete_set.iter().rfold(Vec::new(), |mut vec, v| {
                vec.push(v);
                vec
            }),
            Vec::from_iter((0..256).rev())
        );
    }

    #[test]
    fn test_sum() {
        let set = BitSetVec::from_fn(256, |x| x % 7 == 0 || x % 4 == 0);
        let expected_set = Vec::from_iter((0..256u32).filter(|x| x % 7 == 0 || x % 4 == 0));

        let sum: u32 = set.iter().sum();
        let expected_sum: u32 = expected_set.into_iter().sum();

        assert_eq!(sum, expected_sum);

        assert_eq!(
            BitSetVec::from_first_n(256).iter().sum::<u32>(),
            (0..256).sum::<u32>()
        );
    }

    #[test]
    pub fn from_fn_1() {
        let evens = BitSetVec::from_fn(64, |x| x % 2 == 0);

        assert_eq!(32, evens.count());
        let iter = evens.iter();
        assert_eq!(iter.len(), 32);

        let items: Vec<u32> = iter.collect();
        let expected: Vec<u32> = (0..32u32).map(|x| x * 2).collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn from_iter_1() {
        let expected: Vec<u32> = (0..13u32).map(|x| x * 5).collect();

        let set = BitSetVec::from_iter(expected.iter().copied());

        assert_eq!(13, set.count());

        let iter = set.iter();
        assert_eq!(iter.len(), 13);
        assert_eq!(iter.size_hint(), (13, Some(13)));

        let items: Vec<u32> = iter.collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn reverse_iter_1() {
        let expected: Vec<u32> = (0..13u32).map(|x| x * 5).rev().collect();

        let set = BitSetVec::from_iter(expected.iter().copied());

        assert_eq!(13, set.count());

        let iter = set.iter();
        assert_eq!(iter.len(), 13);
        assert_eq!(iter.size_hint(), (13, Some(13)));

        let items: Vec<u32> = iter.rev().collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn is_empty_1() {
        let mut my_set = BitSetVec::EMPTY;

        assert!(my_set.is_empty());

        my_set.set_bit(63, true);

        assert!(!my_set.is_empty());

        my_set.set_bit(63, false);

        assert!(my_set.is_empty());
    }

    #[test]
    pub fn from_inner_1() {
        let evens = BitSetVec::from_fn(64, |x| x % 2 == 0);
        let inner = evens.clone().into_inner();

        assert_eq!(inner, [6_148_914_691_236_517_205; 1]);
        let again = BitSetVec::from_inner(inner);

        assert_eq!(evens, again);

        let eq = evens.eq(&again);

        assert!(eq);
    }

    #[test]
    pub fn contains_1() {
        let my_set = BitSetVec::from_fn(64, |x| x % 2 == 0);

        for x in 0..70 {
            let value = my_set.contains(x);

            assert_eq!(x % 2 == 0 && x < 64, value);
        }
    }

    #[test]
    pub fn set_bit_1() {
        let mut my_set = BitSetVec::from_fn(64, |x| x % 2 == 0);
        my_set.set_bit(1, true);
        my_set.set_bit(33, true);

        my_set.set_bit(2, false);
        my_set.set_bit(32, false);

        let mut expected: BTreeSet<u32> = (0..32u32).map(|x| x * 2).collect();
        expected.insert(1);
        expected.insert(33);
        expected.remove(&2);
        expected.remove(&32);

        let actual: Vec<_> = my_set.iter().collect();
        let expected: Vec<_> = expected.into_iter().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    pub fn with_bit_set_1() {
        let my_set = BitSetVec::from_fn(64, |x| x % 2 == 0)
            .with_bit_set(1, true)
            .with_bit_set(33, true)
            .with_bit_set(2, false)
            .with_bit_set(32, false);

        let mut expected: BTreeSet<u32> = (0..32u32).map(|x| x * 2).collect();
        expected.insert(1);
        expected.insert(33);
        expected.remove(&2);
        expected.remove(&32);

        let actual: Vec<_> = my_set.iter().collect();
        let expected: Vec<_> = expected.into_iter().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    pub fn union_1() {
        let multiples_of_2 = BitSetVec::from_fn(64, |x| x % 2 == 0);
        let multiples_of_5 = BitSetVec::from_fn(64, |x| x % 5 == 0);
        let multiples_of_2_or_5 = BitSetVec::from_fn(64, |x| x % 2 == 0 || x % 5 == 0);

        let union = multiples_of_2.with_union(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5, union);
    }

    #[test]
    pub fn intersect_1() {
        let multiples_of_2 = BitSetVec::from_fn(64, |x| x % 2 == 0);
        let multiples_of_5 = BitSetVec::from_fn(64, |x| x % 5 == 0);
        let multiples_of_10 = BitSetVec::from_fn(64, |x| x % 10 == 0);
        let multiples_of_6 = BitSetVec::from_fn(64, |x| x % 6 == 0);

        let intersection = multiples_of_2.with_intersect(&multiples_of_5);

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
        let multiples_of_2 = BitSetVec::from_fn(64, |x| x % 2 == 0);
        let multiples_of_5 = BitSetVec::from_fn(64, |x| x % 5 == 0);

        let multiples_of_2_or_5_but_not_10 =
            BitSetVec::from_fn(64, |x| x % 10 != 0 && (x % 2 == 0 || x % 5 == 0));

        let sym_diff = multiples_of_2.with_symmetric_difference(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5_but_not_10, sym_diff);
    }

    #[test]
    fn test_serde_empty() {
        use serde_test::*;
        let v = BitSetVec::EMPTY;

        assert_tokens(
            &v,
            &[
                Token::NewtypeStruct { name: "BitSetVec" },
                Token::Seq { len: Some(0) },
                Token::SeqEnd,
            ],
        );
    }

    #[test]
    fn test_serde_1() {
        use serde_test::*;
        let map = BitSetVec::from_fn(64, |x| x % 2 == 0);

        assert_tokens(
            &map,
            &[
                Token::NewtypeStruct { name: "BitSetVec" },
                Token::Seq { len: Some(1) },
                Token::U64(6_148_914_691_236_517_205),
                Token::SeqEnd,
            ],
        );
    }

    #[test]
    fn test_first1() {
        let mut set = BitSetVec::from_fn(64, |x| x % 2 == 0 || x % 5 == 0);

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
        let mut set = BitSetVec::from_fn(64, |x| x % 2 == 0 || x % 5 == 0);

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
        let mut set = BitSetVec::from_fn(64, |x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..64).filter(|x| x % 2 == 0 || x % 5 == 0).collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(first) = set.pop() {
            actual.push(first);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_pop_last1() {
        let mut set = BitSetVec::from_fn(64, |x| x % 2 == 0 || x % 5 == 0);

        let expected: Vec<_> = (0..64).filter(|x| x % 2 == 0 || x % 5 == 0).rev().collect();

        let mut actual: Vec<_> = Vec::default();

        while let Some(last) = set.pop_last() {
            actual.push(last);
        }

        assert_eq!(expected, actual);
    }

    #[test]
    fn test_display() {
        let mut set = BitSetVec::from_iter([0u32, 1, 99]);

        set.remove(1);
        set.insert(100);

        assert_eq!(set.to_string(), "[0, 99, 100]");
    }

    #[must_use]
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

    // #[test]
    // fn test_iter_subsets() {
    //     let set = BitSetVec::from_iter([0u32, 1, 2, 3, 4]);

    //     for size in 0u32..=5 {
    //         let iter = set.iter_subsets(size);
    //         let expected_len = n_choose_k(set.len(), size);
    //         let results: Vec<_> = iter.collect();

    //         assert_eq!(
    //             results.len(),
    //             expected_len as usize,
    //             "Should be {} results but there were {}. [{}]",
    //             expected_len,
    //             results.len(),
    //             results.iter().fold(String::new(), |mut acc, x| {
    //                 acc.push_str(&x.to_string());
    //                 acc
    //             })
    //         );

    //         for r in &results {
    //             assert_eq!(r.len(), size, "Result should have the correct size");
    //             assert!(r.is_subset(&set), "Result should be a subset of the set");
    //         }

    //         let mut sorted_results = results.clone();
    //         sorted_results.sort();
    //         sorted_results.dedup();

    //         assert_eq!(
    //             results, sorted_results,
    //             "Results should be free of duplicates and sorted"
    //         );
    //     }
    // }

    #[test]
    fn test_from_first_n() {
        let set = BitSetVec::from_first_n(65);

        assert_eq!(65, set.count());
        assert_eq!(set.last(), Some(64));
        assert_eq!(set.into_inner(), [u64::MAX, 1]);
    }

    #[test]
    fn test_swap_bits() {
        let mut set = BitSetVec::from_fn(256, |x| x % 4 == 0);

        set.swap_bits(4, 65);

        set.swap_bits(8, 9);

        assert_eq!(
            set.into_inner(),
            [
                0b1000100010001000100010001000100010001000100010001001000000001,
                0x1111111111111113,
                0x1111111111111111,
                0x1111111111111111
            ]
        );
    }

    #[test]
    fn test_overlaps() {
        let mod3_is0 = BitSetVec::from_fn(256, |x| x % 3 == 0);
        let mod3_is1 = BitSetVec::from_fn(256, |x| x % 3 == 1);

        assert!(!mod3_is0.overlaps(&mod3_is1));
        assert!(!mod3_is1.overlaps(&mod3_is0));

        let mod3_is0_modified = mod3_is0.with_inserted(67);

        assert!(mod3_is0_modified.overlaps(&mod3_is1));
        assert!(mod3_is1.overlaps(&mod3_is0_modified));
    }

    #[test]
    fn test_except_with() {
        let mod3_is0 = BitSetVec::from_fn(256, |x| x % 3 == 0);
        let mod5_is0 = BitSetVec::from_fn(256, |x| x % 5 == 0);

        let actual = mod3_is0.with_except(&mod5_is0);

        let expected = BitSetVec::from_fn(256, |x| x % 3 == 0 && x % 5 != 0);

        assert_eq!(actual.into_inner(), expected.into_inner());
    }

    #[test]
    fn test_nth() {
        let mod20_is0 = BitSetVec::from_fn(128, |x| x % 20 == 0);
        let elements: Vec<Option<u32>> = (0..8).map(|x| mod20_is0.nth(x)).collect();

        assert_eq!(
            elements,
            vec![
                Some(0),
                Some(20),
                Some(40),
                Some(60),
                Some(80),
                Some(100),
                Some(120),
                None
            ]
        );
    }

    #[test]
    fn test_count_lesser_elements() {
        let mod20_is0 = BitSetVec::from_fn(128, |x| x % 20 == 0);

        for x in 0..128 {
            let actual = mod20_is0.count_lesser_elements(x);
            let expected = (x + 19) / 20;
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn test_count_greater_elements() {
        let mod20_is0 = BitSetVec::from_fn(128, |x| x % 20 == 0);

        for x in 0..128 {
            let actual = mod20_is0.count_greater_elements(x);
            let expected = 6 - (x / 20);
            assert_eq!(actual, expected, "x = {x}");
        }
    }

    // #[test]
    // fn test_trailing_zeros() {
    //     assert_eq!(BitSetVec::from_iter([0u32].into_iter()).trailing_zeros(), 0);
    //     assert_eq!(BitSetVec::from_iter([2u32].into_iter()).trailing_zeros(), 2);
    //     assert_eq!(BitSetVec::from_iter([72u32].into_iter()).trailing_zeros(), 72);
    //     assert_eq!(BitSetVec::EMPTY.trailing_zeros(), 128);
    // }

    // #[test]
    // fn test_trailing_ones() {
    //     assert_eq!(BitSetVec::from_iter([1u32].into_iter()).trailing_ones(), 0);
    //     assert_eq!(BitSetVec::from_first_n(2).trailing_ones(), 2);
    //     assert_eq!(BitSetVec::from_first_n(72).trailing_ones(), 72);

    //     assert_eq!(BitSetVec::from_first_n(128).trailing_ones(), 128);
    // }

    // #[test]
    // fn test_leading_zeros() {
    //     assert_eq!(BitSetVec::from_iter([127u32].into_iter()).leading_zeros(), 0);
    //     assert_eq!(BitSetVec::from_iter([126u32].into_iter()).leading_zeros(), 1);
    //     assert_eq!(BitSetVec::from_iter([2u32].into_iter()).leading_zeros(), 125);

    //     assert_eq!(BitSetVec::EMPTY.leading_zeros(), 128);
    // }

    // #[test]
    // fn test_leading_ones() {
    //     assert_eq!(BitSetVec::from_first_n(128).with_removed(127).leading_ones(), 0);
    //     assert_eq!(BitSetVec::from_first_n(128).with_removed(126).leading_ones(), 1);
    //     assert_eq!(BitSetVec::from_first_n(128).with_removed(2).leading_ones(), 125);
    //     assert_eq!(BitSetVec::from_first_n(128).leading_ones(), 128);
    // }

    // #[test]
    // fn test_shift_right() {
    //     let mut set = BitSetVec::from_fn(256, |x| x % 3 == 0);
    //     let expected = BitSetVec::from_fn(256, |x| x % 3 == 1 && x < 128);

    //     set.shift_right(128);

    //     assert_eq!(set, expected);

    //     let mut set2 = BitSetVec::from_fn(256, |x| x % 3 == 0);

    //     //should be the same as before, just in two separate shifts
    //     set2.shift_right(120);
    //     set2.shift_right(8);

    //     assert_eq!(set2, expected);
    // }

    // #[test]
    // fn test_shift_left() {
    //     let mut set = BitSetVec::from_fn(256, |x| x % 3 == 0);
    //     let expected = BitSetVec::from_fn(256, |x| x % 3 == 2 && x >= 128);

    //     set.shift_left(128);

    //     assert_eq!(set, expected);

    //     let mut set2 = BitSetVec::from_fn(256, |x| x % 3 == 0);

    //     //should be the same as before, just in two separate shifts
    //     set2.shift_left(120);
    //     set2.shift_left(8);

    //     assert_eq!(set2, expected);
    // }

    #[test]
    fn test_largest_element_less_than() {
        let set = BitSetVec::from_fn(128, |x| x % 2 == 0);

        for e in 0..=128u32 {
            let expected = if e % 2 == 0 {
                e.checked_sub(2)
            } else {
                e.checked_sub(1)
            };
            let actual = set.largest_element_less_than(e);
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn test_smallest_element_greater_than() {
        let set = BitSetVec::from_fn(128, |x| x % 2 == 0);

        for e in 0..=128u32 {
            let expected = if e % 2 == 0 { e + 2 } else { e + 1 };
            let expected = if expected >= 128 {
                None
            } else {
                Some(expected)
            };
            let actual = set.smallest_element_greater_than(e);
            assert_eq!(actual, expected, "e = {e}");
        }
    }

    #[test]
    fn test_retain(){
        let mut set = BitSetVec::from_fn(256, |x| x % 2 == 0);
        let mut c = 0;
        set.retain(|e|{
            c += e;
            e % 3 ==0
        });

        assert_eq!(c, 16256); //the sum of all even numbers up to 256

        let expected =  BitSetVec::from_fn(256,|x| x % 6 == 0);

        assert_eq!(set, expected)
    }

    #[test]
    fn test_clear() {
        let mut set = BitSetVec::from_fn(256,|x| x % 2 == 0);
        set.clear();
        assert!(set.is_empty())
    }
}
