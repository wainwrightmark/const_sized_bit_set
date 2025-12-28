use crate::SetElement;
use crate::collect_into_bit_set::CollectIntoBitSet;
use crate::prelude::*;
use core::iter::FusedIterator;
use core::num::Wrapping;

#[derive(Debug, Clone, PartialEq)]
pub struct SliceIter<'a> {
    slice: &'a [u64],
    elements_offset: Wrapping<SetElement>,
    first_chunk: u64,
    last_chunk: u64,
}

const WORD_BITS: u32 = u64::BITS;

#[inline]
#[must_use]
const fn first_chunk_bit_to_element(
    element: SetElement,
    elements_offset: Wrapping<SetElement>,
) -> SetElement {
    element.wrapping_add(elements_offset.0)
}

#[inline]
#[must_use]
#[expect(clippy::cast_possible_truncation)]
const fn last_chunk_bit_to_element(
    element: SetElement,
    elements_offset: Wrapping<SetElement>,
    slice: &[u64],
) -> SetElement {
    element
        .wrapping_add(elements_offset.0)
        .wrapping_add(WORD_BITS * (slice.len() as u32 + 1))
}

impl<'a> SliceIter<'a> {
    #[must_use]
    pub const fn new(slice: &'a [u64]) -> Self {
        // We start with empty first and last chunks and the elements offset set one word before zero.
        // This means that when reading exclusively forward or exclusively back (the most common case), the other chunk is never populated.
        // This significantly reduces branch misprediction when reading the final chunk (especially in the backward direction)
        Self {
            slice,
            elements_offset: Wrapping(0u32.wrapping_sub(WORD_BITS)),
            first_chunk: 0,
            last_chunk: 0,
        }
    }

    const fn advance_first_chunk(&mut self) -> Option<()> {
        match self.slice.split_first() {
            Some((new_first_chunk, new_slice)) => {
                self.first_chunk = *new_first_chunk;
                self.slice = new_slice;
                self.elements_offset.0 = self.elements_offset.0.wrapping_add(WORD_BITS);
                Some(())
            }
            None => {
                if self.last_chunk == 0 {
                    None
                } else {
                    self.first_chunk = self.last_chunk;
                    self.last_chunk = 0;
                    self.elements_offset.0 = self.elements_offset.0.wrapping_add(WORD_BITS);
                    Some(())
                }
            }
        }
    }

    pub const fn next_const(&mut self) -> Option<SetElement> {
        loop {
            match {
                let inner: &mut u64 = &mut self.first_chunk;
                let f = super::bit_set_n::BitSet64::pop_const;
                let mut set = BitSet64::from_inner_const(*inner);
                let result = f(&mut set);
                *inner = set.into_inner_const();
                result
            } {
                Some(element) => {
                    return Some(first_chunk_bit_to_element(element, self.elements_offset));
                }
                None => {
                    if let None = self.advance_first_chunk() {
                        return None;
                    }
                }
            }
        }
    }
}

impl Iterator for SliceIter<'_> {
    type Item = SetElement;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.next_const()
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.len()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
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
    fn sum<S>(self) -> S
    where
        Self: Sized,
        S: core::iter::Sum<Self::Item>,
    {
        fn increase_total(word: u64, total: &mut u32, mut multiplier: Wrapping<u32>) {
            if word == u64::MAX {
                *total += word.count_ones() * multiplier.0;
                *total += 2016; //sum of 0..64
            } else {
                let mut value = word;

                while value != 0 {
                    let zeros = value.trailing_zeros();
                    value >>= zeros;
                    multiplier += zeros;
                    let ones = value.trailing_ones(); //there must be some or we wouldn't have shifted right
                    value >>= ones; //cannot overflow as we checked for u64::MAX

                    *total += (ones * (ones + multiplier.0 + multiplier.0 - 1)) / 2;

                    multiplier += ones;
                }
            }
        }

        let mut total = 0u32;
        let mut multiplier = self.elements_offset;
        increase_total(self.first_chunk, &mut total, multiplier);
        multiplier += WORD_BITS;
        for chunk in self.slice {
            increase_total(*chunk, &mut total, multiplier);
            multiplier += WORD_BITS;
        }
        increase_total(self.last_chunk, &mut total, multiplier);

        S::sum(core::iter::once(total))
    }

    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        let mut offset1 = self.elements_offset;
        for word in [self.first_chunk]
            .iter()
            .chain(self.slice)
            .chain([self.last_chunk].iter())
        {
            let mut offset = offset1;
            let mut word = *word;
            if word == u64::MAX {
                for v in offset.0..(offset + (Wrapping(WORD_BITS))).0 {
                    accum = f(accum, v);
                }
            } else {
                while word != 0 {
                    let tz = word.trailing_zeros();
                    word >>= tz;
                    offset += tz;
                    let trailing_ones = word.trailing_ones();
                    for _ in 0..trailing_ones {
                        accum = f(accum, offset.0);
                        offset += 1;
                    }
                    word >>= trailing_ones;
                }
            }
            offset1 += WORD_BITS;
        }
        accum
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        #[expect(clippy::cast_possible_truncation)]
        let mut n = n as u32;

        loop {
            if self.first_chunk == 0 {
                self.advance_first_chunk()?;
            }
            if let Some(new_n) = n.checked_sub(self.first_chunk.count_ones()) {
                n = new_n;
                self.advance_first_chunk()?;
            } else {
                let mut shift = 0;
                loop {
                    let tz = self.first_chunk.trailing_zeros();
                    self.first_chunk >>= tz;
                    shift += tz;
                    let to = self.first_chunk.trailing_ones();
                    if let Some(new_n) = n.checked_sub(to) {
                        n = new_n;
                        self.first_chunk >>= to;
                        shift += to;
                    } else {
                        self.first_chunk >>= n + 1;
                        let r = first_chunk_bit_to_element(shift + n, self.elements_offset);
                        self.first_chunk = self.first_chunk.wrapping_shl(shift + n + 1);

                        return Some(r);
                    }
                }
            }
        }
    }
}
impl FusedIterator for SliceIter<'_> {}
impl ExactSizeIterator for SliceIter<'_> {
    fn len(&self) -> usize {
        (self.first_chunk.count_ones()
            + self.last_chunk.count_ones()
            + self.slice.iter().map(|x| x.count_ones()).sum::<u32>()) as usize
    }
}
impl DoubleEndedIterator for SliceIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match crate::mutate_inner(
                &mut self.last_chunk,
                super::bit_set_n::BitSet64::pop_last_const,
            ) {
                Some(element) => {
                    return Some(last_chunk_bit_to_element(
                        element,
                        self.elements_offset,
                        self.slice,
                    ));
                }
                None => match self.slice.split_last() {
                    Some((new_last_chunk, new_slice)) => {
                        self.last_chunk = *new_last_chunk;
                        self.slice = new_slice;
                    }
                    None => {
                        return crate::mutate_inner(
                            &mut self.first_chunk,
                            super::bit_set_n::BitSet64::pop_last_const,
                        )
                        .map(|element| first_chunk_bit_to_element(element, self.elements_offset));
                    }
                },
            }
        }
    }
    #[expect(clippy::cast_possible_truncation)]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let mut n = n as u32;

        let (chunk, offset): (&mut u64, Wrapping<u32>) = 'l: loop {
            if self.last_chunk == 0 {
                match self.slice.split_last() {
                    Some((new_last_chunk, new_slice)) => {
                        self.last_chunk = *new_last_chunk;
                        self.slice = new_slice;
                    }
                    None => {
                        break 'l (&mut self.first_chunk, self.elements_offset);
                    }
                }
            } else {
                match n.checked_sub(self.last_chunk.count_ones()) {
                    Some(new_n) => {
                        n = new_n;
                        match self.slice.split_last() {
                            Some((new_last_chunk, new_slice)) => {
                                self.last_chunk = *new_last_chunk;
                                self.slice = new_slice;
                            }
                            None => {
                                break 'l (&mut self.first_chunk, self.elements_offset);
                            }
                        }
                    }
                    None => {
                        break 'l (
                            &mut self.last_chunk,
                            (self.elements_offset
                                + Wrapping((self.slice.len() as u32 + 1) * WORD_BITS)),
                        );
                    }
                }
            }
        };

        let mut shift = 0;
        loop {
            if *chunk == 0 {
                return None;
            }
            let lz = chunk.leading_zeros();
            *chunk <<= lz;
            shift += lz;
            let leading_ones = chunk.leading_ones();
            if let Some(new_n) = n.checked_sub(leading_ones) {
                n = new_n;
                *chunk <<= leading_ones;
                shift += leading_ones;
            } else {
                *chunk <<= n + 1;
                let r = (WORD_BITS - (shift + n + 1)).wrapping_add(offset.0);

                *chunk = chunk.wrapping_shr(shift + n + 1);

                return Some(r);
            }
        }
    }
    #[expect(clippy::cast_possible_truncation)]
    fn rfold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        let mut offset1 =
            self.elements_offset + Wrapping((2 + self.slice.len() as u32) * WORD_BITS);
        for word in [self.first_chunk]
            .iter()
            .chain(self.slice)
            .chain([self.last_chunk].iter())
            .rev()
        {
            let mut offset = offset1;
            let mut word = *word;

            if word == u64::MAX {
                for v in ((offset - Wrapping(WORD_BITS)).0..offset.0).rev() {
                    accum = f(accum, v);
                }
            } else {
                while word != 0 {
                    let lz = word.leading_zeros();
                    word <<= lz;
                    offset -= lz;
                    let leading_ones = word.leading_ones();
                    for _ in 0..leading_ones {
                        offset -= 1;
                        accum = f(accum, offset.0);
                    }
                    word <<= leading_ones;
                }
            }
            offset1 -= WORD_BITS;
        }
        accum
    }
}

impl<'a, const WORDS: usize> CollectIntoBitSet<BitSetArray<WORDS>> for SliceIter<'a> {
    fn collect_into_bit_set(self, set: &mut BitSetArray<WORDS>) {
        let mut eo = self.elements_offset;
        for chunk in core::iter::once(self.first_chunk)
            .chain(self.slice.iter().copied())
            .chain(core::iter::once(self.last_chunk))
        {
            if chunk != 0 {
                let index = eo.0 / u64::BITS;
                let word = set.0.get_mut(index as usize).expect("Could not get word");
                *word |= chunk;
            }
            eo += u64::BITS;
        }
    }
}

#[cfg(any(test, feature = "std"))]
impl<'a> CollectIntoBitSet<crate::bit_set_vec::BitSetVec> for SliceIter<'a> {
    fn collect_into_bit_set(self, set: &mut crate::bit_set_vec::BitSetVec) {
        let mut eo = self.elements_offset;
        for chunk in core::iter::once(self.first_chunk)
            .chain(self.slice.iter().copied())
            .chain(core::iter::once(self.last_chunk))
        {
            if chunk != 0 {
                let index = eo.0 / u64::BITS;
                let word = set.get_or_create_word_n(index as usize);
                *word |= chunk;
            }
            eo += u64::BITS;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{collect_into_bit_set::CollectIntoBitSet, prelude::*};

    #[test]
    fn test_both_directions() {
        let arr = BitSetArray::<4>::from_fn(|x| x % 50 == 0);
        let mut iter = arr.iter();

        let mut v = vec![];

        loop {
            let Some(next) = iter.next() else {
                break;
            };
            v.push(next);
            let Some(next_back) = iter.next_back() else {
                break;
            };
            v.push(next_back);
        }

        assert_eq!(v, vec![0, 250, 50, 200, 100, 150]);
    }
    #[test]
    fn test_both_directions2() {
        let arr = BitSetArray::<4>::from_fn(|x| x % 50 == 0);
        let mut iter = arr.iter();

        let mut v = vec![];

        loop {
            let Some(next_back) = iter.next_back() else {
                break;
            };
            v.push(next_back);

            let Some(next) = iter.next() else {
                break;
            };
            v.push(next);
        }

        assert_eq!(v, vec![250, 0, 200, 50, 150, 100]);
    }

    #[test]
    fn test_collect_into_bitset_arr() {
        let arr = BitSetArray::<4>::from_fn(|x| x % 2 == 0);
        let mut collected_arr = BitSetArray::EMPTY;

        let mut iter = arr.iter();

        assert_eq!(100, iter.nth(50).unwrap());

        iter.collect_into_bit_set(&mut collected_arr);

        let expected = BitSetArray::<4>::from_fn(|x| x % 2 == 0 && x > 100);

        assert_eq!(collected_arr, expected);
    }

    #[test]
    fn test_collect_into_bitset_vec() {
        let arr = BitSetVec::from_fn(256, |x| x % 2 == 0);
        let mut collected_arr = BitSetVec::EMPTY;

        let mut iter = arr.iter();

        assert_eq!(100, iter.nth(50).unwrap());

        iter.collect_into_bit_set(&mut collected_arr);

        let expected = BitSetVec::from_fn(256, |x| x % 2 == 0 && x > 100);

        assert_eq!(collected_arr, expected);
    }
}
