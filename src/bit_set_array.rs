use crate::prelude::*;
use crate::slice_iter::SliceIter;
use core::fmt::{Debug, Write};
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
    #[cfg_attr(any(test, feature = "serde"), serde(with = "serde_arrays"))] pub(crate) [u64; WORDS],
);

impl<const WORDS: usize> core::fmt::Display for BitSetArray<WORDS> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_char('[')?;
        let mut write_commas: bool = false;
        for x in self.iter_const() {
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

const WORD_BITS: u32 = u64::BITS;

impl<const WORDS: usize> BitSetArray<WORDS> {
    /// The set where all tiles are missing
    pub const EMPTY: Self = { Self([0; WORDS]) };

    /// The set where all tiles are present
    pub const ALL: Self = { Self([u64::MAX; WORDS]) };

    pub const LAST_WORD: usize = WORDS - 1;

    #[expect(clippy::cast_possible_truncation)]
    const WORDS_U32: u32 = WORDS as u32;

    const CAPACITY: u32 = Self::WORDS_U32 * u64::BITS;

    #[inline]
    #[must_use]
    const fn to_word_and_shift(element: SetElement) -> (usize, SetElement) {
        let word_index = (element / WORD_BITS) as usize;
        let shift = element % WORD_BITS;
        (word_index, shift)
    }

    #[inline]
    #[must_use]
    #[expect(clippy::cast_possible_truncation)]
    const fn to_full_set_element(element: SetElement, word_index: usize) -> SetElement {
        element + (word_index as u32 * WORD_BITS)
    }

    #[inline]
    #[must_use]
    pub fn from_fn<F: FnMut(u32) -> bool>(mut cb: F) -> Self {
        let mut result = Self::default();
        for x in (0..(Self::WORDS_U32 * (WORD_BITS))).filter(|x| cb(*x)) {
            result.insert_const(x);
        }

        result
    }

    #[must_use]
    #[inline]
    pub const fn into_inner_const(self) -> [u64; WORDS] {
        self.0
    }

    #[inline]
    pub const fn from_inner_const(inner: [u64; WORDS]) -> Self {
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
    pub const fn is_empty_const(self) -> bool {
        self.eq(&Self::EMPTY)
    }

    #[must_use]
    #[inline]
    pub const fn is_all_const(self) -> bool {
        self.eq(&Self::ALL)
    }

    #[inline]
    pub const fn clear_const(&mut self) {
        self.0 = Self::EMPTY.0;
    }

    /// Create a set of the elements 0..n
    #[must_use]
    #[inline]
    pub const fn from_first_n_const(n: SetElement) -> Self {
        debug_assert!(
            n <= Self::CAPACITY,
            "Too many elements to create bitset from first n"
        );
        if n == Self::CAPACITY {
            return Self::ALL;
        }

        let full_words = (n / u64::BITS) as usize;

        let mut inner = [0; WORDS];
        let mut i = 0;
        while i < full_words {
            inner[i] = u64::MAX;
            i += 1;
        }
        inner[i] = BitSet64::from_first_n_const(n % u64::BITS).into_inner_const();

        Self(inner)
    }

    #[must_use]
    pub const fn overlaps_const(&self, rhs: &Self) -> bool {
        let mut i = 0usize;
        while i < WORDS {
            if self.0[i] & rhs.0[i] != 0 {
                return true;
            }
            i += 1;
        }
        false
    }

    #[must_use]
    pub const fn iter_const(&self) -> SliceIter<'_> {
        SliceIter::new(&self.0)
    }

    /// Sets the bit at `index` to `bit`
    ///
    /// PANICS if index is out of range
    #[inline]
    pub const fn set_bit(&mut self, index: u32, bit: bool) {
        if bit {
            self.insert_const(index);
        } else {
            self.remove_const(index);
        }
    }

    /// Adds `element` to the set.
    ///
    /// Returns whether `element` was newly inserted.
    ///
    /// PANICS if `element` is out of range
    #[inline]
    pub const fn insert_const(&mut self, element: SetElement) -> bool {
        let (word, shift) = Self::to_word_and_shift(element);
        let mask = 1u64 << shift;
        let r = self.0[word] & mask == 0;

        self.0[word] |= mask;
        r
    }

    /// Toggle the presence of an element.
    /// Returns whether the element is now present.
    ///
    /// PANICS if `element` is out of range
    #[inline]
    pub const fn toggle_const(&mut self, element: SetElement) -> bool {
        let (word, shift) = Self::to_word_and_shift(element);
        let mask = 1u64 << shift;

        self.0[word] ^= mask;
        self.0[word] & mask != 0
    }

    /// If the set contains `element`, remove it from the set.
    /// Returns the element was present.
    ///
    /// PANICS if `element` is out of range
    #[inline]
    pub const fn remove_const(&mut self, element: SetElement) -> bool {
        let (word, shift) = Self::to_word_and_shift(element);
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
    pub const fn with_bit_set(&self, index: u32, bit: bool) -> Self {
        if bit {
            self.with_inserted(index)
        } else {
            self.with_removed(index)
        }
    }

    #[inline]
    pub const fn swap_bits_const(&mut self, i: u32, j: u32) {
        let (i_word_index, i_shift) = Self::to_word_and_shift(i);
        let (j_word_index, j_shift) = Self::to_word_and_shift(j);

        if i_word_index == j_word_index {
            if i_word_index >= WORDS {
                debug_assert!(false, "Index out of range");
                return;
            }
            let word = self.0[i_word_index];
            let mut bs = BitSet64::from_inner_const(word);
            bs.swap_bits_const(i_shift, j_shift);
            self.0[i_word_index] = bs.into_inner_const();
        } else {
            if i_word_index >= WORDS {
                debug_assert!(false, "Index out of range");
                return;
            }
            if j_word_index >= WORDS {
                debug_assert!(false, "Index out of range");
                return;
            }

            let i_word = self.0[i_word_index];
            let j_word = self.0[j_word_index];

            let bit = ((i_word >> i_shift) ^ (j_word >> j_shift)) & 1;

            self.0[i_word_index] = i_word ^ (bit << i_shift);
            self.0[j_word_index] = j_word ^ (bit << j_shift);
        }
    }

    /// PANICS if `element` is out of range
    #[must_use]
    #[inline]
    pub const fn with_inserted(&self, element: SetElement) -> Self {
        let (word, shift) = Self::to_word_and_shift(element);
        let mut arr = self.0;
        arr[word] = self.0[word] | (1u64 << shift);

        Self(arr)
    }

    /// PANICS if `element` is out of range
    #[must_use]
    #[inline]
    pub const fn with_removed(&self, element: SetElement) -> Self {
        let (word, shift) = Self::to_word_and_shift(element);
        let mut arr = self.0;
        arr[word] = self.0[word] & !(1u64 << shift);

        Self(arr)
    }

    #[must_use]
    #[inline]
    #[doc(alias = "get_bit")]
    pub const fn contains_const(&self, element: SetElement) -> bool {
        let (word, shift) = Self::to_word_and_shift(element);

        if word >= WORDS {
            return false;
        }
        let word = self.0[word];

        (word >> shift) & 1 == 1
    }

    #[must_use]
    #[inline]
    pub const fn count_const(&self) -> u32 {
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
    pub const fn count_lesser_elements_const(&self, element: crate::SetElement) -> u32 {
        let index = (element / u64::BITS) as usize;
        let e = element % u64::BITS;
        let mut total = 0u32;

        let mut i = 0;
        while i < index {
            total += self.0[i].count_ones();
            i += 1;
        }
        total += BitSet64::from_inner_const(self.0[index]).count_lesser_elements_const(e);

        total
    }

    #[must_use]
    #[inline]
    pub const fn count_greater_elements_const(&self, element: crate::SetElement) -> u32 {
        let index = (element / u64::BITS) as usize;
        let e = element % u64::BITS;
        let mut total = 0u32;

        let mut i = WORDS - 1;
        while i > index {
            total += self.0[i].count_ones();
            i -= 1;
        }
        total += BitSet64::from_inner_const(self.0[index]).count_greater_elements_const(e);

        total
    }

    #[inline]
    pub const fn intersect_with_const(&mut self, rhs: &Self) {
        let mut word = 0;
        while word < WORDS {
            let r = rhs.0[word];
            self.0[word] &= r;
            word += 1;
        }
    }

    #[inline]
    pub const fn union_with_const(&mut self, rhs: &Self) {
        let mut word = 0;
        while word < WORDS {
            let r = rhs.0[word];
            self.0[word] |= r;
            word += 1;
        }
    }

    #[inline]
    pub const fn except_with_const(&mut self, rhs: &Self) {
        let mut i = 0;
        while i < WORDS {
            self.0[i] &= !rhs.0[i];
            i += 1;
        }
    }

    #[inline]
    #[must_use]
    pub const fn is_subset_const(&self, rhs: &Self) -> bool {
        let mut index = 0;
        while index < WORDS {
            if !BitSet64::from_inner_const(self.0[index])
                .is_subset_const(&BitSet64::from_inner_const(rhs.0[index]))
            {
                return false;
            }
            index += 1;
        }
        true
    }
    #[inline]
    #[must_use]
    pub const fn is_superset(&self, rhs: &Self) -> bool {
        rhs.is_subset_const(self)
    }

    /// Returns a new set containing all elements which belong to one set but not both
    #[inline]
    pub const fn symmetric_difference_with_const(&mut self, rhs: &Self) {
        let mut word = 0;
        while word < WORDS {
            let r = rhs.0[word];
            self.0[word] ^= r;
            word += 1;
        }
    }

    #[inline]
    pub const fn negate_const(&mut self) {
        let mut word = 0;
        while word < WORDS {
            self.0[word] = !self.0[word];
            word += 1;
        }
    }

    #[inline]
    pub const fn reverse_const(&mut self) {
        let Some(mut backward_word) = WORDS.checked_sub(1) else {
            return;
        };
        let mut forward_word = 0usize;

        while forward_word < backward_word {
            let new_b = self.0[forward_word].reverse_bits();
            let new_f = self.0[backward_word].reverse_bits();

            self.0[forward_word] = new_f;
            self.0[backward_word] = new_b;

            forward_word += 1;
            backward_word -= 1;
        }
        if forward_word == backward_word {
            self.0[forward_word] = self.0[forward_word].reverse_bits();
        }
    }

    /// The first (minimum) element in this set
    #[must_use]
    #[inline]
    #[doc(alias = "min")]
    pub const fn first_const(&self) -> Option<u32> {
        let mut word = 0;
        while word < WORDS {
            let tz = self.0[word].trailing_zeros();
            if tz < u64::BITS {
                return Some(Self::to_full_set_element(tz, word));
            }
            word += 1;
        }
        None
    }

    /// The last (maximum) element in this set
    #[must_use]
    #[inline]
    #[doc(alias = "max")]
    pub const fn last_const(&self) -> Option<u32> {
        let mut word = Self::LAST_WORD;

        loop {
            if let Some(index) = (u64::BITS - 1).checked_sub(self.0[word].leading_zeros()) {
                let r = Self::to_full_set_element(index, word);
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
    pub const fn pop_const(&mut self) -> Option<SetElement> {
        let mut word_index = 0;
        while word_index <= Self::LAST_WORD {
            let word = self.0[word_index];
            if word != 0 {
                let tz = word.trailing_zeros();
                let r = Self::to_full_set_element(tz, word_index);
                let t = word & (0u64.wrapping_sub(word));
                self.0[word_index] ^= t;

                return Some(r);
            }
            word_index += 1;
        }
        None
    }

    /// Removes the last (biggest) element of the set and returns it
    /// Returns `None` if the set is empty
    #[must_use]
    #[inline]
    pub const fn pop_last_const(&mut self) -> Option<u32> {
        let mut word_index = Self::LAST_WORD;

        loop {
            let word = self.0[word_index];

            if word != 0 {
                let index = (u64::BITS - 1) - word.leading_zeros();
                let r = Self::to_full_set_element(index, word_index);
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

    /// Return the index of the nth element.
    /// Returns `None` if there are fewer than n+1 elements
    #[must_use]
    #[inline]
    pub const fn nth_const(&self, n: u32) -> Option<u32> {
        let mut word_index = 0;
        let mut n = n;
        while word_index < WORDS {
            if let Some(new_n) = n.checked_sub(self.0[word_index].count_ones()) {
                n = new_n;
                word_index += 1;
                //continue loop
            } else {
                let mut shift = 0;
                let mut word = self.0[word_index];
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
                        let r = Self::to_full_set_element(shift + n, word_index);
                        return Some(r);
                    }
                }
            }
        }
        None
    }

    /// Return the smallest element greater than `index`
    /// Will return `None` if no such element exists
    /// Will return the same regardless of whether `element` is present
    #[must_use]
    #[inline]
    pub const fn smallest_element_greater_than_const(
        &self,
        index: SetElement,
    ) -> Option<SetElement> {
        let mut word = (index / u64::BITS) as usize;
        let e = index % u64::BITS;

        if word >= WORDS {
            return None;
        }

        if let Some(x) =
            BitSet64::from_inner_const(self.0[word]).smallest_element_greater_than_const(e)
        {
            return Some(Self::to_full_set_element(x, word));
        }
        word += 1;

        while word < WORDS {
            let a = BitSet64::from_inner_const(self.0[word]);
            if let Some(x) = a.first_const() {
                return Some(Self::to_full_set_element(x, word));
            }
            word += 1;
        }
        None
    }

    /// Return the largest element less than `index`
    /// Will return `None` if no such element exists
    /// Will return the same regardless of whether `element` is present
    #[must_use]
    #[inline]
    pub const fn largest_element_less_than_const(&self, index: SetElement) -> Option<SetElement> {
        let mut word = (index / u64::BITS) as usize;
        let e = index % u64::BITS;

        if word >= WORDS {
            return self.last_const();
        }

        if let Some(x) = BitSet64::from_inner_const(self.0[word]).largest_element_less_than_const(e)
        {
            return Some(Self::to_full_set_element(x, word));
        }

        match word.checked_sub(1) {
            Some(w) => word = w,
            None => return None,
        }

        loop {
            let a = BitSet64::from_inner_const(self.0[word]);
            if let Some(x) = a.last_const() {
                return Some(Self::to_full_set_element(x, word));
            }

            match word.checked_sub(1) {
                Some(w) => word = w,
                None => return None,
            }
        }
    }

    #[must_use]
    pub const fn trailing_ones_const(&self) -> u32 {
        let mut total = 0;
        let mut i = 0;
        while i < WORDS {
            let word = self.0[i];
            if word == u64::MAX {
                total += u64::BITS;
            } else {
                total += word.trailing_ones();
                return total;
            }
            i += 1;
        }

        total
    }

    /// Equivalent to >>=
    /// Reduce the value of every element in the set by n.
    /// Elements no longer in range are removed.
    pub const fn shift_right_const(&mut self, n: SetElement) {
        let words_shift = (n / u64::BITS) as usize;
        let bits_shift = n % u64::BITS;

        //note we rotate left actually because the bit ordering is opposite to the array ordering
        self.0.rotate_left(words_shift);
        {
            let mut i = WORDS - words_shift;
            while i < WORDS {
                self.0[i] = 0;
                i += 1;
            }
        }

        if bits_shift > 0 {
            let bits_shift_inverse = u64::BITS - bits_shift;
            let mut index_1 = 0;
            loop {
                self.0[index_1] >>= bits_shift;
                let index_2 = index_1 + 1;
                if index_2 < WORDS {
                    self.0[index_1] |= self.0[index_2] << bits_shift_inverse;
                    index_1 = index_2;
                } else {
                    break;
                }
            }
        }
    }

    /// Equivalent to <<=
    /// Increase the value of every element in the set by n.
    /// For finite sets, elements no longer in range are removed.
    pub const fn shift_left_const(&mut self, n: SetElement) {
        let words_shift = (n / u64::BITS) as usize;
        let bits_shift = n % u64::BITS;

        //note we rotate right actually because the bit ordering is opposite to the array ordering
        self.0.rotate_right(words_shift);
        {
            let mut i = 0;
            while i < words_shift {
                self.0[i] = 0;
                i += 1;
            }
        }

        if bits_shift > 0 {
            let bits_shift_inverse = u64::BITS - bits_shift;
            let mut index_1 = WORDS.saturating_sub(1);
            loop {
                self.0[index_1] <<= bits_shift;

                let Some(index_2) = index_1.checked_sub(1) else {
                    break;
                };
                self.0[index_1] |= self.0[index_2] >> bits_shift_inverse;
                index_1 = index_2;
            }
        }
    }
}

impl<const WORDS: usize> Extend<usize> for BitSetArray<WORDS> {
    fn extend<T: IntoIterator<Item = usize>>(&mut self, iter: T) {
        *self = iter.into_iter().fold(*self, |acc: BitSetArray<WORDS>, v| {
            #[expect(clippy::cast_possible_truncation)]
            acc.with_inserted(v as u32)
        });
    }
}

impl<const WORDS: usize> Extend<SetElement> for BitSetArray<WORDS> {
    fn extend<T: IntoIterator<Item = SetElement>>(&mut self, iter: T) {
        *self = iter
            .into_iter()
            .fold(*self, |acc: BitSetArray<WORDS>, v| acc.with_inserted(v));
    }
}

impl<const WORDS: usize> FromIterator<usize> for BitSetArray<WORDS> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = usize>>(iter: T) -> Self {
        #[expect(clippy::cast_possible_truncation)]
        iter.into_iter()
            .fold(Self::default(), |acc, v| acc.with_inserted(v as u32))
    }
}

impl<const WORDS: usize> FromIterator<u32> for BitSetArray<WORDS> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = u32>>(iter: T) -> Self {
        iter.into_iter()
            .fold(Self::default(), |acc, v| acc.with_inserted(v))
    }
}

impl<const WORDS: usize> FiniteBitSet for BitSetArray<WORDS> {
    const ALL: Self = Self::ALL;
    const CAPACITY: u32 = Self::CAPACITY;

    fn negate(&mut self) {
        self.negate_const();
    }

    fn reverse(&mut self) {
        self.reverse_const();
    }

    fn is_all(&self) -> bool {
        self.is_all_const()
    }

    fn trailing_zeros(&self) -> u32 {
        let mut total = 0;
        for i in 0..WORDS {
            let word = self.0[i];
            if word == 0 {
                total += u64::BITS;
            } else {
                total += word.trailing_zeros();
                return total;
            }
        }

        total
    }

    fn leading_zeros(&self) -> u32 {
        let mut total = 0;
        for i in (0..WORDS).rev() {
            let word = self.0[i];
            if word == 0 {
                total += u64::BITS;
            } else {
                total += word.leading_zeros();
                return total;
            }
        }

        total
    }

    fn leading_ones(&self) -> u32 {
        let mut total = 0;
        for i in (0..WORDS).rev() {
            let word = self.0[i];
            if word == u64::MAX {
                total += u64::BITS;
            } else {
                total += word.leading_ones();
                return total;
            }
        }

        total
    }
}

#[cfg(test)]
pub mod tests {
    use crate::bit_set_array::BitSetArray;
    use crate::bit_set_trait::BitSet;
    use crate::finite::FiniteBitSet;
    use std::collections::BTreeSet;

    #[test]
    pub fn from_fn_4() {
        let evens = BitSetArray::<4>::from_fn(|x| x % 2 == 0);

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

        let set = BitSetArray::<4>::from_iter(expected.iter().copied());

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

        let mut set = BitSetArray::<4>::from_iter(multiples_of_5.iter().copied());
        set.extend(multiples_of_4);

        assert_eq!(103, set.count());

        let expected = BitSetArray::<4>::from_fn(|x| x % 4 == 0 || x % 5 == 0);

        assert_eq!(set, expected);
    }

    #[test]
    pub fn reverse_iter_4() {
        let expected: Vec<u32> = (0..52u32).map(|x| x * 5).rev().collect();

        let set = BitSetArray::<4>::from_iter(expected.iter().copied());

        assert_eq!(52, set.count_const());

        let iter = set.iter();
        assert_eq!(iter.len(), 52);
        assert_eq!(iter.size_hint(), (52, Some(52)));

        let items: Vec<u32> = iter.rev().collect();

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
        let inner = evens.into_inner_const();

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
        let mut my_set = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
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
        let my_set = BitSetArray::<4>::from_fn(|x| x % 2 == 0)
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
        let multiples_of_2 = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSetArray::<4>::from_fn(|x| x % 5 == 0);
        let multiples_of_2_or_5 = BitSetArray::<4>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let union = multiples_of_2.with_union(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5, union);
    }

    #[test]
    pub fn intersect_4() {
        let multiples_of_2 = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSetArray::<4>::from_fn(|x| x % 5 == 0);
        let multiples_of_10 = BitSetArray::<4>::from_fn(|x| x % 10 == 0);
        let multiples_of_6 = BitSetArray::<4>::from_fn(|x| x % 6 == 0);

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
        let multiples_of_2 = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSetArray::<4>::from_fn(|x| x % 5 == 0);

        let multiples_of_2_or_5_but_not_10 =
            BitSetArray::<4>::from_fn(|x| x % 10 != 0 && (x % 2 == 0 || x % 5 == 0));

        let sym_diff = multiples_of_2.with_symmetric_difference(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5_but_not_10, sym_diff);
    }

    #[test]
    pub fn negate_4() {
        let evens = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        let odds = BitSetArray::<4>::from_fn(|x| x % 2 == 1);

        let negated_evens = evens.with_negated();

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
        let iter = set.iter();
        assert_eq!(iter.last(), Some(252));
    }

    #[test]
    fn test_iter_max4() {
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0 && x < 140);
        let iter = set.iter();
        let max = Iterator::max(iter);
        assert_eq!(max, Some(133));
    }

    #[test]
    fn test_iter_min4() {
        let set = BitSetArray::<4>::from_fn(|x| x > 64 && x % 7 == 0);
        let iter = set.iter();
        let min = Iterator::min(iter);
        assert_eq!(min, Some(70));
    }

    #[test]
    fn test_iter_nth_4() {
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0);
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
        let set = BitSetArray::<1>::from_fn(|x| x == 63);
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
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0);
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
    fn test_iter_nth_back_empty() {
        let set = BitSetArray::<4>::EMPTY;
        assert_eq!(set.iter().nth_back(100), None);
    }

    #[test]
    fn test_iter_fold4() {
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0);
        let iter = set.iter();
        let fold_result = iter.fold(13, |acc, x| acc + x);

        assert_eq!(fold_result, 4675);

        let complete_set = BitSetArray::<4>::ALL;

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
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0);
        let iter = set.iter();
        let fold_result = iter.rfold(13, |acc, x| acc + x);

        assert_eq!(fold_result, 4675);

        let complete_set = BitSetArray::<4>::ALL;

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
        let set = BitSetArray::<4>::from_fn(|x| x % 7 == 0 || x % 4 == 0);
        let expected_set = Vec::from_iter((0..256u32).filter(|x| x % 7 == 0 || x % 4 == 0));

        let sum: u32 = set.iter().sum();
        let expected_sum: u32 = expected_set.iter().sum();

        assert_eq!(sum, expected_sum);

        assert_eq!(
            BitSetArray::<4>::ALL.iter().sum::<u32>(),
            (0..256).sum::<u32>()
        );
    }

    #[test]
    pub fn from_fn_1() {
        let evens = BitSetArray::<1>::from_fn(|x| x % 2 == 0);

        assert_eq!(32, evens.count_const());
        let iter = evens.iter();
        assert_eq!(iter.len(), 32);

        let items: Vec<u32> = iter.collect();
        let expected: Vec<u32> = (0..32u32).map(|x| x * 2).collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn from_iter_1() {
        let expected: Vec<u32> = (0..13u32).map(|x| x * 5).collect();

        let set = BitSetArray::<1>::from_iter(expected.iter().copied());

        assert_eq!(13, set.count_const());

        let iter = set.iter();
        assert_eq!(iter.len(), 13);
        assert_eq!(iter.size_hint(), (13, Some(13)));

        let items: Vec<u32> = iter.collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn reverse_iter_1() {
        let expected: Vec<u32> = (0..13u32).map(|x| x * 5).rev().collect();

        let set = BitSetArray::<1>::from_iter(expected.iter().copied());

        assert_eq!(13, set.count_const());

        let iter = set.iter();
        assert_eq!(iter.len(), 13);
        assert_eq!(iter.size_hint(), (13, Some(13)));

        let items: Vec<u32> = iter.rev().collect();

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
        let inner = evens.into_inner_const();

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
        let my_set = BitSetArray::<1>::from_fn(|x| x % 2 == 0)
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
        let multiples_of_2 = BitSetArray::<1>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSetArray::<1>::from_fn(|x| x % 5 == 0);
        let multiples_of_2_or_5 = BitSetArray::<1>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let union = multiples_of_2.with_union(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5, union);
    }

    #[test]
    pub fn intersect_1() {
        let multiples_of_2 = BitSetArray::<1>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSetArray::<1>::from_fn(|x| x % 5 == 0);
        let multiples_of_10 = BitSetArray::<1>::from_fn(|x| x % 10 == 0);
        let multiples_of_6 = BitSetArray::<1>::from_fn(|x| x % 6 == 0);

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
        let multiples_of_2 = BitSetArray::<1>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSetArray::<1>::from_fn(|x| x % 5 == 0);

        let multiples_of_2_or_5_but_not_10 =
            BitSetArray::<1>::from_fn(|x| x % 10 != 0 && (x % 2 == 0 || x % 5 == 0));

        let sym_diff = multiples_of_2.with_symmetric_difference(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5_but_not_10, sym_diff);
    }

    #[test]
    pub fn negate_1() {
        let evens = BitSetArray::<1>::from_fn(|x| x % 2 == 0);
        let odds = BitSetArray::<1>::from_fn(|x| x % 2 == 1);

        let negated_evens = evens.with_negated();

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
        let mut set = BitSetArray::<2>::from_iter([0u32, 1, 99]);

        set.remove(1);
        set.insert(100);

        assert_eq!(set.to_string(), "[0, 99, 100]");
    }

    #[test]
    fn test_iter_subsets() {
        let set = BitSetArray::<1>::from_iter([0u32, 1, 2, 3, 4]);

        for size in 0u32..=5 {
            let iter = set.iter_subsets(size);
            let expected_len = set.count_subsets(size);
            let results: Vec<_> = iter.collect();

            assert_eq!(
                results.len(),
                expected_len as usize,
                "Should be {} results but there were {}. [{}]",
                expected_len,
                results.len(),
                results.iter().fold(String::new(), |mut acc, x| {
                    acc.push_str(&x.to_string());
                    acc
                })
            );

            for r in &results {
                assert_eq!(r.count_const(), size, "Result should have the correct size");
                assert!(r.is_subset(&set), "Result should be a subset of the set");
            }

            let mut sorted_results = results.clone();
            sorted_results.sort();
            sorted_results.dedup();

            assert_eq!(
                results, sorted_results,
                "Results should be free of duplicates and sorted"
            );
        }
    }

    #[test]
    fn test_from_first_n() {
        let set = BitSetArray::<4>::from_first_n(65);

        assert_eq!(65, set.count());
        assert_eq!(set.last(), Some(64));
        assert_eq!(set.into_inner(), [u64::MAX, 1, 0, 0,]);

        assert_eq!(BitSetArray::<2>::from_first_n_const(128), BitSetArray::ALL);
    }

    #[test]
    fn test_swap_bits() {
        let mut set = BitSetArray::<4>::from_fn(|x| x % 4 == 0);

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
        let mod3_is0 = BitSetArray::<4>::from_fn(|x| x % 3 == 0);
        let mod3_is1 = BitSetArray::<4>::from_fn(|x| x % 3 == 1);

        assert!(!mod3_is0.overlaps(&mod3_is1));
        assert!(!mod3_is1.overlaps(&mod3_is0));

        let mod3_is0_modified = mod3_is0.with_inserted(67);

        assert!(mod3_is0_modified.overlaps(&mod3_is1));
        assert!(mod3_is1.overlaps(&mod3_is0_modified));
    }

    #[test]
    fn test_except_with() {
        let mod3_is0 = BitSetArray::<2>::from_fn(|x| x % 3 == 0);
        let mod5_is0 = BitSetArray::<2>::from_fn(|x| x % 5 == 0);

        let actual = mod3_is0.with_except(&mod5_is0);

        let expected = BitSetArray::<2>::from_fn(|x| x % 3 == 0 && x % 5 != 0);

        assert_eq!(actual.into_inner(), expected.into_inner());
    }

    #[test]
    fn test_nth() {
        let mod20_is0 = BitSetArray::<2>::from_fn(|x| x % 20 == 0);
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
        let mod20_is0 = BitSetArray::<2>::from_fn(|x| x % 20 == 0);

        for x in 0..128 {
            let actual = mod20_is0.count_lesser_elements(x);
            let expected = (x + 19) / 20;
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn test_count_greater_elements() {
        let mod20_is0 = BitSetArray::<2>::from_fn(|x| x % 20 == 0);

        for x in 0..128 {
            let actual = mod20_is0.count_greater_elements(x);
            let expected = 6 - (x / 20);
            assert_eq!(actual, expected, "x = {x}");
        }
    }

    #[test]
    fn test_trailing_zeros() {
        assert_eq!(
            BitSetArray::<2>::from_iter([0u32].into_iter()).trailing_zeros(),
            0
        );
        assert_eq!(
            BitSetArray::<2>::from_iter([2u32].into_iter()).trailing_zeros(),
            2
        );
        assert_eq!(
            BitSetArray::<2>::from_iter([72u32].into_iter()).trailing_zeros(),
            72
        );
        assert_eq!(BitSetArray::<2>::EMPTY.trailing_zeros(), 128);
    }

    #[test]
    fn test_trailing_ones() {
        assert_eq!(
            BitSetArray::<2>::from_iter([1u32].into_iter()).trailing_ones(),
            0
        );
        assert_eq!(BitSetArray::<2>::from_first_n_const(2).trailing_ones(), 2);
        assert_eq!(BitSetArray::<2>::from_first_n_const(72).trailing_ones(), 72);

        assert_eq!(BitSetArray::<2>::ALL.trailing_ones(), 128);
    }

    #[test]
    fn test_leading_zeros() {
        assert_eq!(
            BitSetArray::<2>::from_iter([127u32].into_iter()).leading_zeros(),
            0
        );
        assert_eq!(
            BitSetArray::<2>::from_iter([126u32].into_iter()).leading_zeros(),
            1
        );
        assert_eq!(
            BitSetArray::<2>::from_iter([2u32].into_iter()).leading_zeros(),
            125
        );

        assert_eq!(BitSetArray::<2>::EMPTY.leading_zeros(), 128);
    }

    #[test]
    fn test_leading_ones() {
        assert_eq!(
            BitSetArray::<2>::from_iter([127u32].into_iter())
                .with_negated()
                .leading_ones(),
            0
        );
        assert_eq!(
            BitSetArray::<2>::from_iter([126u32].into_iter())
                .with_negated()
                .leading_ones(),
            1
        );
        assert_eq!(
            BitSetArray::<2>::from_iter([2u32].into_iter())
                .with_negated()
                .leading_ones(),
            125
        );
        assert_eq!(BitSetArray::<2>::ALL.leading_ones(), 128);
    }

    #[test]
    fn test_shift_right() {
        let mut set = BitSetArray::<8>::from_fn(|x| x % 3 == 0);
        let expected = BitSetArray::<8>::from_fn(|x| x % 3 == 1 && x < 384);

        set.shift_right(128);

        assert_eq!(set, expected);

        let mut set2 = BitSetArray::<8>::from_fn(|x| x % 3 == 0);

        //should be the same as before, just in two separate shifts
        set2.shift_right(120);
        set2.shift_right(8);

        assert_eq!(set2, expected);
    }

    #[test]
    fn test_shift_left() {
        let mut set = BitSetArray::<8>::from_fn(|x| x % 3 == 0);
        let expected = BitSetArray::<8>::from_fn(|x| x % 3 == 2 && x >= 128);

        set.shift_left(128);

        assert_eq!(set, expected);

        let mut set2 = BitSetArray::<8>::from_fn(|x| x % 3 == 0);

        //should be the same as before, just in two separate shifts
        set2.shift_left(120);
        set2.shift_left(8);

        assert_eq!(set2, expected);
    }

    #[test]
    fn test_largest_element_less_than() {
        let set = BitSetArray::<2>::from_fn(|x| x % 2 == 0);

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
        let set = BitSetArray::<2>::from_fn(|x| x % 2 == 0);

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
    fn test_reverse() {
        let set4 = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        let expected_set4 = BitSetArray::<4>::from_fn(|x| x % 2 == 1);

        assert_eq!(set4.with_reversed(), expected_set4);

        let set5 = BitSetArray::<5>::from_fn(|x| x % 2 == 0);
        let expected_set5 = BitSetArray::<5>::from_fn(|x| x % 2 == 1);

        assert_eq!(set5.with_reversed(), expected_set5);
    }

    #[test]
    fn test_retain() {
        let mut set = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        let mut c = 0;
        set.retain(|e| {
            c += e;
            e % 3 == 0
        });

        assert_eq!(c, 16256);

        let expected = BitSetArray::<4>::from_fn(|x| x % 6 == 0);

        assert_eq!(set, expected);
    }

    #[test]
    fn test_clear() {
        let mut set = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        set.clear_const();
        assert!(set.is_empty_const());
    }
}
