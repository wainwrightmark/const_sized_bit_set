use crate::SetElement;
use core::iter::FusedIterator;

#[derive(Debug, Clone, PartialEq)]
pub struct SliceIter<'a> {
    slice: &'a [u64],
    elements_offset: SetElement,
    first_chunk: u64,
    last_chunk: u64,
}

const WORD_BITS: u32 = u64::BITS;

#[inline]
#[must_use]
const fn first_chunk_bit_to_element(
    element: SetElement,
    elements_offset: SetElement,
) -> SetElement {
    element + elements_offset
}

#[inline]
#[must_use]
#[expect(clippy::cast_possible_truncation)]
const fn last_chunk_bit_to_element(
    element: SetElement,
    elements_offset: SetElement,
    slice: &[u64],
) -> SetElement {
    element + elements_offset + (WORD_BITS * (slice.len() as u32 + 1))
}

impl<'a> SliceIter<'a> {
    pub const fn new(slice: &'a [u64]) -> Self {
        match slice.split_first() {
            Some((&first_chunk, remaining_slice)) => Self {
                slice: remaining_slice,
                elements_offset: 0,
                first_chunk,
                last_chunk: 0,
            },
            None => Self {
                slice,
                elements_offset: 0,
                first_chunk: 0,
                last_chunk: 0,
            },
        }
    }

    const fn advance_first_chunk(&mut self) -> Option<()> {
        match self.slice.split_first() {
            Some((new_first_chunk, new_slice)) => {
                self.first_chunk = *new_first_chunk;
                self.slice = new_slice;
                self.elements_offset += WORD_BITS;
                Some(())
            }
            None => {
                if self.last_chunk == 0 {
                    return None;
                } else {
                    self.first_chunk = self.last_chunk;
                    self.last_chunk = 0;
                    self.elements_offset += WORD_BITS;
                    Some(())
                }
            }
        }
    }

    //todo const functions e.g. next
}

impl<'a> Iterator for SliceIter<'a> {
    type Item = SetElement;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match crate:: mutate_inner(&mut self.first_chunk, |x| x.pop_const()) {
                Some(element) => {
                    return Some(first_chunk_bit_to_element(element, self.elements_offset));
                }
                None => {
                    self.advance_first_chunk()?;
                }
            }
        }
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
        let mut total = 0u32;
        let mut multiplier = self.elements_offset;

        fn increase_total(word: u64, total: &mut u32, mut multiplier: u32) {
            if word == u64::MAX {
                *total += word.count_ones() * multiplier;
                *total += 2016; //sum of 0..64
            } else {
                let mut value = word;

                while value != 0 {
                    let zeros = value.trailing_zeros();
                    value >>= zeros;
                    multiplier += zeros;
                    let ones = value.trailing_ones(); //there must be some or we wouldn't have shifted right
                    value >>= ones; //cannot overflow as we checked for u64::MAX

                    *total += (ones * (ones + multiplier + multiplier - 1)) / 2;

                    multiplier += ones;
                }
            }
        }
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
                for v in offset..(offset + (WORD_BITS)) {
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
            match n.checked_sub(self.first_chunk.count_ones()) {
                Some(new_n) => {
                    n = new_n;
                    self.advance_first_chunk()?
                }
                None => {
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
                            #[expect(clippy::cast_possible_truncation)]
                            let r = first_chunk_bit_to_element(shift + n, self.elements_offset);
                            self.first_chunk = self.first_chunk.wrapping_shl(shift + n + 1);

                            return Some(r);
                        }
                    }
                }
            }
        }
    }
}
impl<'a> FusedIterator for SliceIter<'a> {}
impl<'a> ExactSizeIterator for SliceIter<'a> {
    fn len(&self) -> usize {
        (self.first_chunk.count_ones()
            + self.last_chunk.count_ones()
            + self.slice.iter().map(|x| x.count_ones()).sum::<u32>()) as usize
    }
}
impl<'a> DoubleEndedIterator for SliceIter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match crate::mutate_inner(&mut self.last_chunk, |x| x.pop_last_const()) {
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
                        return crate::mutate_inner(&mut self.first_chunk, |x| x.pop_last_const()).map(
                            |element| first_chunk_bit_to_element(element, self.elements_offset),
                        );
                    }
                },
            }
        }
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        #[expect(clippy::cast_possible_truncation)]
        let mut n = n as u32;

        let (chunk, offset): (&mut u64, u32) = 'l: loop {
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
                            (self.elements_offset + ((self.slice.len() as u32 + 1) * WORD_BITS)),
                        );
                    }
                }
            }
        };

        let mut shift = 0;
        loop {
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
                let r = (WORD_BITS - (shift + n + 1)) + offset;

                *chunk = chunk.wrapping_shr(shift + n + 1);

                return Some(r);
            }
        }
    }

    fn rfold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        let mut offset1 = self.elements_offset + ((2 + self.slice.len() as u32) * WORD_BITS);
        for word in [self.first_chunk]
            .iter()
            .chain(self.slice)
            .chain([self.last_chunk].iter())
            .rev()
        {
            let mut offset = offset1;
            let mut word = *word;

            if word == u64::MAX {
                for v in ((offset - (WORD_BITS))..offset).rev() {
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
                        accum = f(accum, offset);
                    }
                    word <<= leading_ones;
                }
            }
            offset1 -= WORD_BITS;
        }
        accum
    }
}
