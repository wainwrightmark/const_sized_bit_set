use crate::{bit_set_iterator::BitSetIterator, SetElement};
#[cfg(any(test, feature = "serde"))]
use serde::{Deserialize, Serialize};

macro_rules! define_bit_set_n {
    ($name:ident, $inner: ty) => {
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
            #[must_use]
            pub const fn contains_const(&self, element: SetElement) -> bool {
                debug_assert!(
                    element < Self::MAX_COUNT,
                    "Element is too big to be contained in bitset"
                );
                (self.0 >> element) & 1 == 1
            }

            /// Whether two sets are equal
            #[inline]
            #[must_use]
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
                debug_assert!(
                    element < Self::MAX_COUNT,
                    "Element is too big to insert into bitset"
                );

                let mask = 1 << element;
                let r = self.0 & mask == 0;

                self.0 |= mask;
                r
            }

            /// Remove an element from the set
            #[inline]
            pub const fn remove_const(&mut self, element: SetElement) -> bool {
                debug_assert!(
                    element < Self::MAX_COUNT,
                    "Element is too big to remove from bitset"
                );
                let mask = 1 << element;
                let r = self.0 & mask != 0;
                self.0 &= !mask;
                r
            }

            /// Create a set of the elements 0..n
            #[must_use]
            #[inline]
            pub const fn from_first_n_const(n: SetElement) -> Self {
                debug_assert!(
                    n <= Self::MAX_COUNT,
                    "Too many elements to create bitset from first n"
                );

                if n == Self::MAX_COUNT {
                    Self::ALL
                } else {
                    let inner = !(<$inner>::MAX << n);
                    Self(inner)
                }
            }

            /// Swap the bits at i and j
            #[inline]
            pub const fn swap_bits_const(&mut self, i: SetElement, j: SetElement) {
                debug_assert!(
                    i <= Self::MAX_COUNT,
                    "Element i is too big to swap in bitset"
                );
                debug_assert!(
                    j <= Self::MAX_COUNT,
                    "Element J is too big to swap in bitset"
                );

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

            #[must_use]
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

            type IntoIter = BitSetIterator<Self>;

            fn into_iter(self) -> Self::IntoIter {
                BitSetIterator(self)
            }
        }
    };
}

define_bit_set_n!(BitSet8, u8);
define_bit_set_n!(BitSet16, u16);
define_bit_set_n!(BitSet32, u32);
define_bit_set_n!(BitSet64, u64);
define_bit_set_n!(BitSet128, u128);

#[cfg(test)]
mod tests {
    use crate::{bit_set_n::BitSet16, bit_set_trait::BitSetTrait};

    #[test]
    fn test_serde_empty() {
        use serde_test::*;
        let set = BitSet16::EMPTY;

        assert_tokens(
            &set,
            &[Token::NewtypeStruct { name: "BitSet16" }, Token::U16(0)],
        );
    }

    #[test]
    fn test_serde() {
        use serde_test::*;
        let set = BitSet16::from_fn(|x| x % 2 == 1);

        assert_tokens(
            &set,
            &[
                Token::NewtypeStruct { name: "BitSet16" },
                Token::U16(0b1010101010101010),
            ],
        );
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

        assert!(BitSet16::from_inner(0b1101).is_superset_const(&BitSet16::from_inner(0b0101)));

        assert!(BitSet16::from_inner(0b1101).overlaps_const(&BitSet16::from_inner(0b0101)));

        assert!(!BitSet16::from_inner(0b1010).overlaps_const(&BitSet16::from_inner(0b0101)));

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
