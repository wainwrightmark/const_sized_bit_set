use std::ops::Shr;

#[must_use]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitSet<const WORDS: usize>([u64; WORDS]);

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

    pub const fn from_inner(inner: [u64; WORDS]) -> Self {
        Self(inner)
    }

    #[must_use]
    #[inline]
    pub const fn eq(&self, rhs: &Self) -> bool {
        let mut index = 0;
        loop {
            if index >= WORDS {
                break;
            }
            if self.0[index] != rhs.0[index] {
                return false;
            }
            index += 1;
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
        let word = index / 64;
        let shift = (index % 64) as u32;

        if bit {
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
        let word = index / 64;
        let shift = (index % 64) as u32;

        let inner = if bit {
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
        let word_index = index / 64;
        let shift = (index % 64) as u32;

        if word_index >= WORDS {
            return false;
        }
        let word = self.0[word_index];

        (word >> shift) & 1 == 1
    }

    #[must_use]
    pub const fn count(&self) -> u32 {
        let mut count: u32 = 0;
        let mut index = 0;
        loop {
            if index >= WORDS {
                break;
            }

            count += self.0[index].count_ones();
            index += 1;
        }

        count
    }

    #[must_use]
    pub const fn intersect(&self, rhs: &Self) -> Self {
        let mut arr = self.0;
        let mut index = 0;
        loop {
            if index >= WORDS {
                break;
            }
            let r = rhs.0[index];
            arr[index] &= r;
            index += 1;
        }

        Self(arr)
    }

    #[must_use]
    pub const fn union(&self, rhs: &Self) -> Self {
        let mut arr = self.0;
        let mut index = 0;
        loop {
            if index >= WORDS {
                break;
            }
            let r = rhs.0[index];
            arr[index] |= r;
            index += 1;
        }

        Self(arr)
    }

    #[must_use]
    pub const fn is_subset(&self, rhs: &Self) -> bool {
        self.intersect(rhs).eq(self) //todo check one word at a time
    }

    #[must_use]
    pub const fn is_superset(&self, rhs: &Self) -> bool {
        rhs.is_subset(self)
    }

    /// Returns a new set containing all elements which belong to one set but not both
    #[must_use]
    pub const fn symmetric_difference(&self, rhs: &Self) -> Self {
        let mut arr = self.0;
        let mut index = 0;
        loop {
            if index >= WORDS {
                break;
            }
            let r = rhs.0[index];
            arr[index] ^= r;
            index += 1;
        }

        Self(arr)
    }

    #[must_use]
    pub const fn negate(&self) -> Self {
        let mut arr = [0; WORDS];
        let mut index = 0;
        loop {
            if index >= WORDS {
                break;
            }

            arr[index] = !self.0[index];
            index += 1;
        }

        Self(arr)
    }
}

impl<const WORDS: usize> IntoIterator for BitSet<WORDS> {
    type Item = usize;

    type IntoIter = BitSetIter<WORDS>;

    fn into_iter(self) -> Self::IntoIter {
        BitSetIter {
            data: self.0,
            skip: 0,
        }
    }
}

#[must_use]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitSetIter<const WORDS: usize> {
    data: [u64; WORDS],
    skip: u32,
}

impl<const WORDS: usize> ExactSizeIterator for BitSetIter<WORDS> {}

impl<const WORDS: usize> Iterator for BitSetIter<WORDS> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        let mut word_index = self.skip / u64::BITS;
        let mut word: &mut u64;
        loop {
            word = self.data.get_mut(word_index as usize)?;
            if *word != 0 {
                break;
            }
            word_index += 1;
            self.skip = word_index * u64::BITS;
        }

        let tz = word.trailing_zeros();
        let r = self.skip + tz;
        *word = word.shr(tz + 1);
        self.skip = r + 1;

        Some(r as usize)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let c = self.count();
        (c, Some(c))
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        let word_index = (self.skip / u64::BITS) as usize;
        let mut total = 0;
        for x in word_index..WORDS {
            total += self.data[x].count_ones();
        }
        total as usize
    }
}

#[cfg(test)]
pub mod tests {
    use std::collections::BTreeSet;

    use crate::BitSet;

    #[test]
    pub fn from_fn() {
        let evens = BitSet::<4>::from_fn(|x| x % 2 == 0);

        assert_eq!(128, evens.count());
        let iter = evens.into_iter();
        assert_eq!(iter.count(), 128);

        let items: Vec<usize> = iter.collect();
        let expected: Vec<usize> = (0..128usize).map(|x| x * 2).collect();

        assert_eq!(items, expected);
    }

    #[test]
    pub fn from_iter() {
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
    pub fn is_empty() {
        let mut my_set = BitSet::<4>::EMPTY;

        assert!(my_set.is_empty());

        my_set.set_bit(255, true);

        assert!(!my_set.is_empty());

        my_set.set_bit(255, false);

        assert!(my_set.is_empty());
    }

    #[test]
    pub fn from_inner() {
        let evens = BitSet::<4>::from_fn(|x| x % 2 == 0);
        let inner = evens.into_inner();

        assert_eq!(inner, [6148914691236517205; 4]);
        let again = BitSet::from_inner(inner);

        assert_eq!(evens, again);

        let eq = evens.eq(&again);

        assert!(eq);
    }

    #[test]
    pub fn get_bit() {
        let my_set = BitSet::<4>::from_fn(|x| x % 2 == 0);

        for x in 0..260 {
            let value = my_set.get_bit(x);

            assert_eq!(x % 2 == 0 && x < 256, value);
        }
    }

    #[test]
    pub fn set_bit() {
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
    pub fn with_bit_set() {
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
    pub fn union(){
        let multiples_of_2 = BitSet::<4>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSet::<4>::from_fn(|x| x % 5 == 0);
        let multiples_of_2_or_5 = BitSet::<4>::from_fn(|x| x % 2 == 0 || x % 5 == 0);

        let union = multiples_of_2.union(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5, union);

    }

    #[test]
    pub fn intersect() {
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
    pub fn symmetric_difference() {
        let multiples_of_2 = BitSet::<4>::from_fn(|x| x % 2 == 0);
        let multiples_of_5 = BitSet::<4>::from_fn(|x| x % 5 == 0);

        let multiples_of_2_or_5_but_not_10 =
            BitSet::<4>::from_fn(|x| x % 10 != 0 && (x % 2 == 0 || x % 5 == 0));

        let sym_diff = multiples_of_2.symmetric_difference(&multiples_of_5);

        assert_eq!(multiples_of_2_or_5_but_not_10, sym_diff);
    }

    #[test]
    pub fn negate() {
        let evens = BitSet::<4>::from_fn(|x| x % 2 == 0);
        let odds = BitSet::<4>::from_fn(|x| x % 2 == 1);

        let negated_evens = evens.negate();

        assert_eq!(negated_evens, odds);
    }
}
