use core::{
    fmt::{Binary, Debug, LowerHex, UpperHex},
    iter::FusedIterator,
};

#[cfg(any(test, feature = "serde"))]
use serde::{Deserialize, Serialize};

type Inner64 = u64;

/// A map from integers to integers
#[must_use]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(any(test, feature = "serde"), derive(Serialize, Deserialize))]
pub struct BitMap64<const BITS_PER_NUMBER: u32>(Inner64);

impl<const BITS_PER_NUMBER: u32> UpperHex for BitMap64<BITS_PER_NUMBER> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        UpperHex::fmt(&self.0, f)
    }
}

impl<const BITS_PER_NUMBER: u32> LowerHex for BitMap64<BITS_PER_NUMBER> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        LowerHex::fmt(&self.0, f)
    }
}

impl<const BITS_PER_NUMBER: u32> Binary for BitMap64<BITS_PER_NUMBER> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Binary::fmt(&self.0, f)
    }
}

impl<const BITS_PER_NUMBER: u32> Debug for BitMap64<BITS_PER_NUMBER> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list()
            .entries((0..Self::ENTRIES).map(|key| self.get(key)))
            .finish()
    }
}

impl<const BITS_PER_NUMBER: u32> FromIterator<Inner64> for BitMap64<BITS_PER_NUMBER> {
    fn from_iter<T: IntoIterator<Item = Inner64>>(iter: T) -> Self {
        let mut set = Self(0);

        for (key, value) in iter.into_iter().enumerate() {
            #[expect(clippy::cast_possible_truncation)]
            set.insert(key as u32, value);
        }
        set
    }
}

impl<const BITS_PER_NUMBER: u32> Default for BitMap64<BITS_PER_NUMBER> {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl<const BITS_PER_NUMBER: u32> IntoIterator for BitMap64<BITS_PER_NUMBER> {
    type Item = Inner64;

    type IntoIter = BitMapIterator64<BITS_PER_NUMBER>;

    fn into_iter(self) -> Self::IntoIter {
        BitMapIterator64 {
            index: 0,
            inner_map: self,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Hash)]
pub struct BitMapIterator64<const BITS_PER_NUMBER: u32> {
    inner_map: BitMap64<BITS_PER_NUMBER>,
    index: u32,
}

impl<const BITS_PER_NUMBER: u32> FusedIterator for BitMapIterator64<BITS_PER_NUMBER> {}

impl<const BITS_PER_NUMBER: u32> ExactSizeIterator for BitMapIterator64<BITS_PER_NUMBER> {}

impl<const BITS_PER_NUMBER: u32> Iterator for BitMapIterator64<BITS_PER_NUMBER> {
    type Item = Inner64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= BitMap64::<BITS_PER_NUMBER>::ENTRIES {
            return None;
        }

        let v = self.inner_map.get(self.index);
        self.index += 1;
        Some(v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let a = BitMap64::<BITS_PER_NUMBER>::ENTRIES.saturating_sub(self.index) as usize;
        (a, Some(a))
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        
        BitMap64::<BITS_PER_NUMBER>::ENTRIES.saturating_sub(self.index) as usize
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        if self.index >= BitMap64::<BITS_PER_NUMBER>::ENTRIES {
            return None;
        }
        let v = self.inner_map.get(BitMap64::<BITS_PER_NUMBER>::ENTRIES - 1);
        Some(v)
    }

    #[expect(clippy::cast_possible_truncation)]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.index += n as u32;
        self.next()
    }

    fn max(self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        if self.index >= BitMap64::<BITS_PER_NUMBER>::ENTRIES {
            return None;
        }

        let mut i = self.inner_map;
        i.clear_first_n(self.index);
        Some(i.max_pair().1)
    }

    fn min(self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        if self.index >= BitMap64::<BITS_PER_NUMBER>::ENTRIES {
            return None;
        }

        let mut i = self.inner_map;
        i.maximize_first_n(self.index);

        let min = i.min_pair().1;

        Some(min)
    }

    fn sum<S>(self) -> S
    where
        Self: Sized,
        S: core::iter::Sum<Self::Item>,
    {
        let mut i = self.inner_map;
        i.clear_first_n(self.index);
        let sum = Inner64::from(i.sum());
        S::sum([sum].into_iter())
    }
}

impl<const BITS_PER_NUMBER: u32> DoubleEndedIterator for BitMapIterator64<BITS_PER_NUMBER> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index >= BitMap64::<BITS_PER_NUMBER>::ENTRIES {
            return None;
        }
        let r = self.inner_map.get(BitMap64::<BITS_PER_NUMBER>::ENTRIES - 1);
        self.index += 1;
        self.inner_map.0 <<= BITS_PER_NUMBER;
        Some(r)
    }

    #[expect(clippy::cast_possible_truncation)]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.index += n as u32;
        self.inner_map.0 <<= n as u32 * BITS_PER_NUMBER;
        self.next_back()
    }
}

//#[expect(unused_variables)]
impl<const BITS_PER_NUMBER: u32> BitMap64<BITS_PER_NUMBER> {
    pub const EMPTY: Self = Self(0);

    pub const ENTRIES: u32 = Inner64::BITS / BITS_PER_NUMBER;

    pub(crate) const ELEMENT_0_MASK: u64 = Inner64::MAX >> (Inner64::BITS - BITS_PER_NUMBER);

    pub(crate) const BASE: u64 = Self::ELEMENT_0_MASK + 1;

    pub const LSB_MASK: u64 = {
        let mut mask = 0;
        let mut shifted = 0;
        while shifted < Inner64::BITS {
            mask |= 1;
            mask <<= BITS_PER_NUMBER;
            shifted += BITS_PER_NUMBER;
        }
        mask |= 1;
        mask
    };

    pub(crate) const MSB_MASK: u64 = Self::LSB_MASK << (BITS_PER_NUMBER - 1);

    #[must_use] pub const fn get(&self, key: u32) -> Inner64 {
        let shift = key * BITS_PER_NUMBER;

        let i = self.0 >> shift;
        i & Self::ELEMENT_0_MASK
    }

    pub const fn insert(&mut self, key: u32, value: Inner64) {
        let shift = key * BITS_PER_NUMBER;

        let mut new_inner = self.0;
        new_inner &= (!Self::ELEMENT_0_MASK).rotate_left(shift);

        new_inner |= (value & Self::ELEMENT_0_MASK) << shift;
        self.0 = new_inner;
    }

    ///Sets the value at the given index to zero
    pub const fn remove(&mut self, key: u32) {
        let shift = key * BITS_PER_NUMBER;
        let shifted_mask = (!Self::ELEMENT_0_MASK).rotate_left(shift);
        let mut new_inner = self.0;

        new_inner &= shifted_mask;
        self.0 = new_inner;
    }

    pub const fn clear(&mut self) {
        self.0 = 0;
    }

    ///Set the first n elements to 0
    pub const fn clear_first_n(&mut self, n: u32) {
        if n >= Self::ENTRIES {
            self.clear();
            return;
        }
        let shift = n * BITS_PER_NUMBER;
        self.0 = self.0.wrapping_shr(shift);
        self.0 = self.0.wrapping_shl(shift);
    }

    pub(crate) const fn maximize_first_n(&mut self, n: u32) {
        if n >= Self::ENTRIES {
            self.clear();

            return;
        }
        self.negate();
        let shift = n * BITS_PER_NUMBER;
        self.0 = self.0.wrapping_shr(shift);
        self.0 = self.0.wrapping_shl(shift);
        self.negate();
    }

    pub const fn negate(&mut self) {
        //TODO remove extra bits on uneven maps
        self.0 = !self.0;
    }

    /// The inner value of the set
    #[must_use]
    #[inline]
    pub const fn inner(&self) -> Inner64 {
        self.0
    }

    /// Creates a new set from an inner value
    #[must_use]
    #[inline]
    pub const fn from_inner(inner: Inner64) -> Self {
        Self(inner)
    }

    /// Creates a new set where every value is set to a given amount
    #[must_use]
    #[inline]
    pub const fn with_values(value: Inner64) -> Self {
        Self(Self::LSB_MASK * (value & Self::ELEMENT_0_MASK))
    }

    pub(crate) const EVEN_VALUES_MASK: Inner64 = {
        let mut mask = 0;
        let mut shifted = 0;
        let shift_amount = BITS_PER_NUMBER * 2;

        while shifted < Inner64::BITS {
            mask |= Self::ELEMENT_0_MASK;
            mask <<= shift_amount;
            shifted += shift_amount;
        }
        mask |= Self::ELEMENT_0_MASK;
        mask
    };

    pub(crate) const ODD_VALUES_MASK: Inner64 = {
        //TODO remove extra bits on uneven maps
        !Self::EVEN_VALUES_MASK
    };

    pub(crate) const EVEN_BASES: Inner64 = Self::ODD_VALUES_MASK & Self::LSB_MASK;
    pub(crate) const ODD_BASES: Inner64 = Self::EVEN_VALUES_MASK & Self::LSB_MASK;

    pub const fn wrapping_add(&self, other: &Self) -> Self {
        let evens = (self.0 & Self::EVEN_VALUES_MASK)
            .wrapping_add(other.0 & Self::EVEN_VALUES_MASK)
            & Self::EVEN_VALUES_MASK;

        let odds = (self.0 & Self::ODD_VALUES_MASK).wrapping_add(other.0 & Self::ODD_VALUES_MASK)
            & Self::ODD_VALUES_MASK;

        Self(evens | odds)
    }

    pub const fn wrapping_sub(&self, other: &Self) -> Self {
        let evens = (self.0 & Self::EVEN_VALUES_MASK)
            .wrapping_add(Self::EVEN_BASES.wrapping_sub(other.0 & Self::EVEN_VALUES_MASK))
            & Self::EVEN_VALUES_MASK;

        let odds = (self.0 & Self::ODD_VALUES_MASK)
            .wrapping_add(Self::ODD_BASES.wrapping_sub(other.0 & Self::ODD_VALUES_MASK))
            & Self::ODD_VALUES_MASK;

        Self(evens | odds)
    }

    //pub const fn saturating_add(&self, other: &Self) -> Self {todo!()}
    //pub const fn saturating_sub(&self, other: &Self) -> Self {todo!()}

    /// Return a new set where the value of each element is the highest value of that element from either set
    pub fn union(&self, other: &Self) -> Self {
        let self_good_bits = self.0 | !other.0;
        let other_good_bits = other.0 | !self.0;
        let mut main_mask = Self::MSB_MASK;
        let mut self_mask = main_mask & self_good_bits;
        let mut other_mask = main_mask & other_good_bits;

        let mut shift = 1;

        while shift < BITS_PER_NUMBER {
            self_mask >>= 1;
            other_mask >>= 1;
            main_mask >>= 1;

            let swap = (self_mask & self_good_bits) | (!other_mask & main_mask);
            other_mask = (other_mask & other_good_bits) | (!self_mask & main_mask);
            self_mask = swap;
            shift += 1;
        }

        self_mask *= Self::ELEMENT_0_MASK;

        let from_self = self_mask & self.0;
        let from_other = !self_mask & other.0;
        Self(from_self | from_other)
    }

    /// Return a new set where the value of each element is the lowest value of that element from either set
    pub const fn intersection(&self, other: &Self) -> Self {
        let self_good_bits = self.0 | !other.0;
        let other_good_bits = other.0 | !self.0;
        let mut main_mask = Self::MSB_MASK;
        let mut self_mask = main_mask & self_good_bits;
        let mut other_mask = main_mask & other_good_bits;

        let mut shift = 1;

        while shift < BITS_PER_NUMBER {
            self_mask >>= 1;
            other_mask >>= 1;
            main_mask >>= 1;

            let swap = (self_mask & self_good_bits) | (!other_mask & main_mask);
            other_mask = (other_mask & other_good_bits) | (!self_mask & main_mask);
            self_mask = swap;
            shift += 1;
        }

        self_mask *= Self::ELEMENT_0_MASK;

        let from_self = !self_mask & self.0;
        let from_other = self_mask & other.0;
        Self(from_self | from_other)
    }

    /// Returns the (key, value) pair of the minimal element with the lowest key
    #[must_use] pub const fn min_pair(&self) -> (u32, Inner64) {
        if self.0 == 0 {
            return (0, 0);
        }

        let neg_inner = !self.0;

        let mut current_mask = Self::MSB_MASK;
        let new_mask = current_mask & neg_inner;
        if new_mask != 0 {
            current_mask = new_mask;
        }

        let mut shift = 1;

        while shift < BITS_PER_NUMBER {
            current_mask >>= 1;
            let new_mask = current_mask & neg_inner;
            if new_mask != 0 {
                current_mask = new_mask;
            }
            shift += 1;
        }

        let key = current_mask.trailing_zeros() / BITS_PER_NUMBER;
        let value = (self.0 >> current_mask.trailing_zeros()) & Self::ELEMENT_0_MASK;
        (key, value)
    }

    /// Returns the (key, value) pair of the maximal element with the lowest key
    #[must_use] pub const fn max_pair(&self) -> (u32, Inner64) {
        if self.0 == 0 {
            return (0, 0);
        }

        let mut current_mask = Self::MSB_MASK;
        let new_mask = current_mask & self.0;
        if new_mask != 0 {
            current_mask = new_mask;
        }

        let mut shift = 1;

        while shift < BITS_PER_NUMBER {
            current_mask >>= 1;
            let new_mask = current_mask & self.0;
            if new_mask != 0 {
                current_mask = new_mask;
            }
            shift += 1;
        }

        let key = current_mask.trailing_zeros() / BITS_PER_NUMBER;
        let value = (self.0 >> current_mask.trailing_zeros()) & Self::ELEMENT_0_MASK;
        (key, value)
    }

    const MSB_VALUE: u32 = 2u32.pow(BITS_PER_NUMBER - 1);
    /// The sum of all counts in the set
    #[must_use] pub const fn sum(&self) -> u32 {
        let mut sum = 0;
        let mut mask = Self::LSB_MASK;
        let mut multiple = 1;

        while multiple <= Self::MSB_VALUE {
            let masked = self.0 & mask;
            sum += masked.count_ones() * multiple;
            //shift += 1;
            multiple *= 2;
            mask <<= 1;
        }

        sum
    }

    /// Set every value that is current at least 1 to `new_value`
    pub fn flatten(&mut self, new_value: Inner64) {
        let mut set_bits = Self::MSB_MASK & self.0;
        let mut mask = Self::MSB_MASK;

        let mut shift = 1;
        while shift < BITS_PER_NUMBER {
            set_bits >>= 1;
            mask >>= 1;
            set_bits |= self.0 & mask;
            shift += 1;
        }

        let new_inner = set_bits * (new_value & Self::ELEMENT_0_MASK);
        self.0 = new_inner;
    }

    #[must_use] pub fn find_index_of_value(&self, value: Inner64)-> Option<u32>{
        // `mapped` will be 1 on bits with the correct value.
        let mapped = !((Self::LSB_MASK * value) ^ self.0);
        // We are looking for entries which are all 1s

        let mut current = Self::MSB_MASK & mapped;
        let mut shift = 1;
        while shift < BITS_PER_NUMBER {
            current >>= 1;
            current &= mapped;
            shift += 1;
        }

        if current== 0{
            return None;
        }

        let r = current.trailing_zeros() / BITS_PER_NUMBER;
        Some(r)
    }


    pub const fn wrapping_increment(&mut self, key: u32, amount: Inner64) {
        let shift = key * BITS_PER_NUMBER;
        let i = self.0 >> shift;
        let v = i & Self::ELEMENT_0_MASK;
        let value = v.wrapping_add(amount & Self::ELEMENT_0_MASK) & Self::ELEMENT_0_MASK;
        let new_mask = (value ^ v) << shift;
        self.0 ^= new_mask;
    }

    pub fn wrapping_decrement(&mut self, key: u32, amount: Inner64) {
        let shift = key * BITS_PER_NUMBER;
        let i = self.0 >> shift;
        let v = i & Self::ELEMENT_0_MASK;
        let value =
            v.wrapping_add(Self::BASE - (amount & Self::ELEMENT_0_MASK)) & Self::ELEMENT_0_MASK;
        let new_mask = (value ^ v) << shift;
        self.0 ^= new_mask;
    }

    // pub fn saturating_increment(&mut self, key: u32, amount: Inner64) {
    //     let shift = key * BITS_PER_NUMBER;
    //     let i = self.0 >> shift;
    //     let v = i & Self::ELEMENT_0_MASK;
    //     let value = v.wrapping_add(amount & Self::ELEMENT_0_MASK).min(Self::ELEMENT_0_MASK);
    //     let new_mask = (value ^ v) << shift;
    //     self.0 ^= new_mask;
    // }

    // pub fn saturating_decrement(&mut self, key: u32, amount: Inner64) {
    //     todo!()
    // }

    // pub fn checked_increment(&mut self, key: u32, amount: Inner64)-> bool {
    //     todo!()
    // }

    // pub fn checked_decrement(&mut self, key: u32, amount: Inner64)-> bool {
    //     todo!()
    // }
}

#[cfg(test)]
mod tests {

    use super::BitMap64;

    #[test]
    pub fn test_masks() {
        assert_eq!(BitMap64::<4>::ELEMENT_0_MASK, 0b1111);
        assert_eq!(BitMap64::<8>::ELEMENT_0_MASK, 0b11111111);

        assert_eq!(BitMap64::<8>::LSB_MASK, 0x0101010101010101);
        assert_eq!(BitMap64::<4>::LSB_MASK, 0x1111111111111111);

        assert_eq!(BitMap64::<8>::MSB_MASK, 0x8080808080808080);
        assert_eq!(BitMap64::<4>::MSB_MASK, 0x8888888888888888);

        assert_eq!(BitMap64::<8>::EVEN_VALUES_MASK, 0xff00ff00ff00ff);
        assert_eq!(BitMap64::<4>::EVEN_VALUES_MASK, 0xf0f0f0f0f0f0f0f);
    }

    #[test]
    pub fn test_get() {
        let mut set: BitMap64<4> = BitMap64::default();

        for x in 0..16 {
            assert_eq!(set.get(x), 0);
        }

        set.insert(0, 3);

        assert_eq!(set.inner(), 3);

        assert_eq!(set.get(0), 3);

        for x in 1..16 {
            assert_eq!(set.get(x), 0);
        }
        //random sequence
        let sequence: [u64; 16] = [13, 2, 9, 4, 12, 2, 2, 12, 0, 14, 7, 8, 12, 15, 1, 10];

        let set: BitMap64<4> = BitMap64::from_iter(sequence);

        for (key, value) in sequence.into_iter().enumerate() {
            let v = set.get(key as u32);
            assert_eq!(v, value, "Value at {key} was {v}, expected {value}");
        }
    }

    #[test]
    pub fn test_wrapping_increment() {
        let sequence1: [u64; 16] = [13, 2, 9, 4, 12, 2, 2, 12, 0, 14, 7, 8, 12, 15, 1, 10];
        let sequence2: [u64; 16] = [0, 5, 4, 11, 7, 5, 6, 1, 6, 3, 15, 1, 5, 14, 3, 9];

        let expected_values: [u64; 16] =
            std::array::from_fn(|x| (sequence1[x] + sequence2[x]) % 16);

        let mut set: BitMap64<4> = BitMap64::from_iter(sequence1);

        for (key, value) in sequence2.into_iter().enumerate() {
            set.wrapping_increment(key as u32, value);
            let v = set.get(key as u32);
            let expected = expected_values[key];

            assert_eq!(
                v, expected,
                "Stage 1: Value at {key} was {v}, expected {expected}"
            );
        }

        for (key, value) in expected_values.into_iter().enumerate() {
            let v = set.get(key as u32);
            assert_eq!(
                v, value,
                "Stage 2: Value at {key} was {v}, expected {value}"
            );
        }
    }

    #[test]
    pub fn test_wrapping_decrement() {
        let sequence1: [u64; 16] = [13, 2, 9, 4, 12, 2, 2, 12, 0, 14, 7, 8, 12, 15, 1, 10];
        let sequence2: [u64; 16] = [0, 5, 4, 11, 7, 5, 6, 1, 6, 3, 15, 1, 5, 14, 3, 9];

        let expected_values: [u64; 16] =
            std::array::from_fn(|x| (sequence1[x] + 16 - sequence2[x]) % 16);

        let mut set: BitMap64<4> = BitMap64::from_iter(sequence1);

        for (key, value) in sequence2.into_iter().enumerate() {
            set.wrapping_decrement(key as u32, value);
            let v = set.get(key as u32);
            let expected = expected_values[key];

            assert_eq!(
                v, expected,
                "Stage 1: Value at {key} was {v}, expected {expected}"
            );
        }

        for (key, value) in expected_values.into_iter().enumerate() {
            let v = set.get(key as u32);
            assert_eq!(
                v, value,
                "Stage 2: Value at {key} was {v}, expected {value}"
            );
        }
    }

    #[test]
    fn test_max() {
        let sequence1: [u64; 16] = [0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14, 15];

        let set: BitMap64<4> = BitMap64::EMPTY;

        assert_eq!(set.max_pair(), (0, 0));

        let set: BitMap64<4> = BitMap64::from_iter(sequence1);

        assert_eq!(set.max_pair(), (7, 15));
    }

    #[test]
    fn test_min() {
        let sequence1: [u64; 16] = [15, 14, 13, 1, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 2];

        let set: BitMap64<4> = BitMap64::EMPTY;

        assert_eq!(set.min_pair(), (0, 0));

        let set: BitMap64<4> = BitMap64::from_iter(sequence1);

        assert_eq!(set.min_pair(), (3, 1));
    }

    #[test]
    fn test_sum() {
        let sequence1: [u64; 16] = [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0];

        let set: BitMap64<4> = BitMap64::from_iter(sequence1);

        assert_eq!(set.sum(), 120);
    }

    #[test]
    fn test_with_values() {
        let sequence1: [u64; 16] = [11; 16];
        let set1 = BitMap64::<4>::from_iter(sequence1);

        let set2 = BitMap64::<4>::with_values(11);

        assert_eq!(set1, set2);
    }

    #[test]
    fn test_wrapping_add() {
        let sequence1: [u64; 16] = [13, 2, 9, 4, 12, 2, 2, 12, 0, 14, 7, 8, 12, 15, 1, 10];
        let sequence2: [u64; 16] = [0, 5, 4, 11, 7, 5, 6, 1, 6, 3, 15, 1, 5, 14, 3, 9];

        let expected: [u64; 16] = std::array::from_fn(|x| (sequence1[x] + sequence2[x]) % 16);
        let expected = BitMap64::<4>::from_iter(expected);
        let set1 = BitMap64::<4>::from_iter(sequence1);
        let set2 = BitMap64::<4>::from_iter(sequence2);

        let result = set1.wrapping_add(&set2);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_wrapping_sub() {
        let sequence1: [u64; 16] = [13, 2, 9, 4, 12, 2, 2, 12, 0, 14, 7, 8, 12, 15, 1, 10];
        let sequence2: [u64; 16] = [0, 5, 4, 11, 7, 5, 6, 1, 6, 3, 15, 1, 5, 14, 3, 9];

        let expected: [u64; 16] = std::array::from_fn(|x| (16 + sequence1[x] - sequence2[x]) % 16);
        let expected = BitMap64::<4>::from_iter(expected);
        let set1 = BitMap64::<4>::from_iter(sequence1);
        let set2 = BitMap64::<4>::from_iter(sequence2);

        let result = set1.wrapping_sub(&set2);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_union() {
        let sequence1: [u64; 16] = [13, 2, 9, 4, 12, 2, 2, 12, 0, 14, 7, 8, 12, 15, 1, 10];
        let sequence2: [u64; 16] = [0, 5, 4, 11, 7, 5, 6, 1, 6, 3, 15, 1, 5, 14, 3, 9];

        // let sequence1: [u64; 16] = [0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0];
        // let sequence2: [u64; 16] = [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0];

        let expected: [u64; 16] = std::array::from_fn(|x| sequence1[x].max(sequence2[x]));
        let expected = BitMap64::<4>::from_iter(expected);
        let set1 = BitMap64::<4>::from_iter(sequence1);
        let set2 = BitMap64::<4>::from_iter(sequence2);

        let result = set1.union(&set2);

        assert_eq!(
            result, expected,
            r"
            Expected {expected:?}
            Result   {result:?}
            Set1     {set1:?}
            Set2     {set2:?}
            "
        );
    }

    #[test]
    fn test_intersection() {
        let sequence1: [u64; 16] = [13, 2, 9, 4, 12, 2, 2, 12, 0, 14, 7, 8, 12, 15, 1, 10];
        let sequence2: [u64; 16] = [0, 5, 4, 11, 7, 5, 6, 1, 6, 3, 15, 1, 5, 14, 3, 9];

        // let sequence1: [u64; 16] = [0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0];
        // let sequence2: [u64; 16] = [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0];

        let expected: [u64; 16] = std::array::from_fn(|x| sequence1[x].min(sequence2[x]));
        let expected = BitMap64::<4>::from_iter(expected);
        let set1 = BitMap64::<4>::from_iter(sequence1);
        let set2 = BitMap64::<4>::from_iter(sequence2);

        let result = set1.intersection(&set2);

        assert_eq!(
            result, expected,
            r"
            Expected {expected:?}
            Result   {result:?}
            Set1     {set1:?}
            Set2     {set2:?}
            "
        );
    }

    #[test]
    fn test_flatten() {
        let sequence1: [u64; 16] = [13, 2, 9, 4, 0, 0, 2, 12, 0, 14, 7, 8, 12, 15, 1, 0];

        let new_value = 7;

        let expected: [u64; 16] =
            std::array::from_fn(|x| if sequence1[x] > 0 { new_value } else { 0 });
        let expected = BitMap64::<4>::from_iter(expected);

        let mut set1 = BitMap64::<4>::from_iter(sequence1);
        set1.flatten(new_value);

        assert_eq!(set1, expected);
    }

    #[test]
    fn test_clear() {
        let sequence1: [u64; 16] = [13, 2, 9, 4, 0, 0, 2, 12, 0, 14, 7, 8, 12, 15, 1, 0];

        let mut set1 = BitMap64::<4>::from_iter(sequence1);

        set1.clear();

        assert_eq!(set1, BitMap64::from_inner(0));
    }

    #[test]
    fn test_clear_first_n() {
        let sequence1: [u64; 16] = [13, 2, 9, 4, 0, 0, 2, 12, 0, 14, 7, 8, 12, 15, 1, 0];

        let mut set1 = BitMap64::<4>::from_iter(sequence1);

        set1.clear_first_n(5);

        assert_eq!(
            set1,
            BitMap64::<4>::from_iter([0, 0, 0, 0, 0, 0, 2, 12, 0, 14, 7, 8, 12, 15, 1, 0])
        );
    }

    #[test]
    fn test_remove() {
        let sequence1: [u64; 16] = [13, 2, 9, 4, 0, 0, 2, 12, 0, 14, 7, 8, 12, 15, 1, 14];
        let mut set1 = BitMap64::<4>::from_iter(sequence1);

        set1.remove(3);
        set1.remove(15);

        assert_eq!(
            set1,
            BitMap64::<4>::from_iter([13, 2, 9, 0, 0, 0, 2, 12, 0, 14, 7, 8, 12, 15, 1, 0])
        );
    }

    #[test]
    fn test_iterator() {
        let sequence1: [u64; 16] = [13, 2, 9, 4, 0, 0, 2, 12, 0, 14, 7, 8, 12, 15, 1, 14];
        let set1 = BitMap64::<4>::from_iter(sequence1);

        let collected: Vec<_> = set1.clone().into_iter().collect();

        assert_eq!(collected, sequence1);

        assert_eq!(set1.clone().into_iter().count(), 16);
        assert_eq!(set1.clone().into_iter().size_hint(), (16, Some(16)));

        assert_eq!(set1.clone().into_iter().last(), Some(14));
        assert_eq!(set1.clone().into_iter().max(), Some(15));
        assert_eq!(set1.clone().into_iter().min(), Some(0));
        assert_eq!(set1.clone().into_iter().sum::<u64>(), 113u64);
        assert_eq!(set1.clone().into_iter().next_back(), Some(14u64));

        let mut exhausted_iter = set1.clone().into_iter();
        assert_eq!(exhausted_iter.nth(15), Some(14));
        assert_eq!(exhausted_iter.next(), None);
        assert_eq!(exhausted_iter.clone().count(), 0);
        assert_eq!(exhausted_iter.clone().last(), None);
        assert_eq!(exhausted_iter.clone().max(), None);
        assert_eq!(exhausted_iter.clone().min(), None);
        assert_eq!(exhausted_iter.clone().sum::<u64>(), 0u64);
        assert_eq!(exhausted_iter.clone().next_back(), None);

        let mut half_exhausted_iter = set1.clone().into_iter();
        assert_eq!(half_exhausted_iter.nth(10), Some(7));

        assert_eq!(half_exhausted_iter.clone().count(), 5);
        assert_eq!(half_exhausted_iter.clone().last(), Some(14));
        assert_eq!(half_exhausted_iter.clone().max(), Some(15));
        assert_eq!(half_exhausted_iter.clone().min(), Some(1));
        assert_eq!(half_exhausted_iter.clone().sum::<u64>(), 50u64);
        assert_eq!(half_exhausted_iter.clone().next_back(), Some(14));


        let mut reverse_iter = set1.clone().into_iter().rev();
        let mut expected_reverse_iter = sequence1.into_iter().rev();

        assert_eq!(reverse_iter.clone().collect::<Vec<_>>(), expected_reverse_iter.clone().collect::<Vec<_>>() );

        assert_eq!(reverse_iter.nth(4), expected_reverse_iter.nth(4));
        assert_eq!(reverse_iter.nth(3), expected_reverse_iter.nth(3));
        assert_eq!(reverse_iter.nth(6), expected_reverse_iter.nth(6));
        assert_eq!(reverse_iter.nth(6), expected_reverse_iter.nth(6));
    }

    #[test]
    fn test_formatting(){
        let sequence1: [u64; 16] = [13, 2, 9, 4, 0, 0, 2, 12, 0, 14, 7, 8, 12, 15, 1, 14];
        let set1 = BitMap64::<4>::from_iter(sequence1);

        assert_eq!(format!("{set1:X}"), "E1FC87E0C200492D");
        assert_eq!(format!("{set1:x}"), "e1fc87e0c200492d");
        assert_eq!(format!("{set1:b}"), "1110000111111100100001111110000011000010000000000100100100101101");
        assert_eq!(format!("{set1:?}"), "[13, 2, 9, 4, 0, 0, 2, 12, 0, 14, 7, 8, 12, 15, 1, 14]");
    }

    #[test]
    fn test_index_of_value(){
        let sequence1: [u64; 16] = [13, 2, 9, 4, 0, 0, 2, 12, 0, 14, 7, 8, 12, 15, 1, 14];
        let set1 = BitMap64::<4>::from_iter(sequence1);


        for value in 0u64..16{
            let expected = sequence1.iter().position(|x| *x== value).map(|x| x as u32);
            let actual =set1.find_index_of_value(value);

            assert_eq!(expected, actual, "Index of {value}");
        }
    }
}
