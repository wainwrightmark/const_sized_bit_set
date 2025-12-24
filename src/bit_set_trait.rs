use core::iter::FusedIterator;

use crate::{BitSet8, BitSet16, BitSet32, BitSet64, BitSet128, BitSetArray, SetElement};

pub trait BitSet: Sized {
    type Inner;

    const EMPTY: Self;
    ///Returns the number of set bits in the set.
    fn count(&self) -> u32;

    fn into_inner(self) -> Self::Inner;
    fn from_inner(inner: Self::Inner) -> Self;

    fn from_first_n(n: u32) -> Self;

    fn is_empty(&self) -> bool;

    fn clear(&mut self);

    fn contains(&self, element: SetElement) -> bool;

    #[doc(alias = "min")]
    fn first(&self) -> Option<SetElement>;

    #[doc(alias = "max")]
    fn last(&self) -> Option<SetElement>;

    fn pop(&mut self) -> Option<SetElement>;

    fn pop_last(&mut self) -> Option<SetElement>;

    fn iter<'a>(
        &'a self,
    ) -> impl Iterator<Item = SetElement> + Clone + FusedIterator + DoubleEndedIterator + ExactSizeIterator;

    /// Sets the `element` to `bit`.
    /// Returns whether the element was changed
    fn set_bit(&mut self, element: SetElement, bit: bool) -> bool {
        if bit {
            self.insert(element)
        } else {
            self.remove(element)
        }
    }
    #[must_use]
    fn with_bit_set(&self, element: SetElement, bit: bool) -> Self
    where
        Self: Clone,
    {
        let mut s = self.clone();
        s.set_bit(element, bit);
        s
    }

    /// Insert an element into the set
    /// Returns whether the element was inserted (it was not already present)
    fn insert(&mut self, element: SetElement) -> bool;

    #[must_use]
    fn with_inserted(&self, element: SetElement) -> Self
    where
        Self: Clone,
    {
        let mut s = self.clone();
        s.insert(element);
        s
    }

    /// Remove an element from the set
    /// Returns whether the element was removed (was previously present)
    fn remove(&mut self, element: SetElement) -> bool;

    #[must_use]
    fn with_removed(&self, element: SetElement) -> Self
    where
        Self: Clone,
    {
        let mut s = self.clone();
        s.remove(element);
        s
    }

    fn swap_bits(&mut self, i: u32, j: u32);

    #[must_use]
    fn with_bits_swapped(&self, i: u32, j: u32) -> Self
    where
        Self: Clone,
    {
        let mut s = self.clone();
        s.swap_bits(i, j);
        s
    }

    fn is_subset(&self, rhs: &Self) -> bool;
    fn is_superset(&self, rhs: &Self) -> bool {
        rhs.is_subset(self)
    }
    fn overlaps(&self, rhs: &Self) -> bool;

    fn intersect_with(&mut self, rhs: &Self);

    #[must_use]
    fn with_intersect(&self, rhs: &Self) -> Self
    where
        Self: Clone,
    {
        let mut s = self.clone();
        s.intersect_with(rhs);
        s
    }

    fn union_with(&mut self, rhs: &Self);
    #[must_use]
    fn with_union(&self, rhs: &Self) -> Self
    where
        Self: Clone,
    {
        let mut s = self.clone();
        s.union_with(rhs);
        s
    }

    fn except_with(&mut self, rhs: &Self);

    #[must_use]
    fn with_except(&self, rhs: &Self) -> Self
    where
        Self: Clone,
    {
        let mut s = self.clone();
        s.except_with(rhs);
        s
    }

    ///Changes this set to contain only the elements that are either currently present or present in `rhs` but not both.
    fn symmetric_difference_with(&mut self, rhs: &Self);

    #[must_use]
    fn with_symmetric_difference(&self, rhs: &Self) -> Self
    where
        Self: Clone,
    {
        let mut s = self.clone();
        s.symmetric_difference_with(rhs);
        s
    }

    /// Return the set of minimal members according to a function
    #[must_use]
    fn min_set_by_key<K: Ord>(&self, f: impl Fn(SetElement) -> K) -> Self {
        let mut result_set = Self::EMPTY;
        let mut iter = self.iter();

        let Some(first) = iter.next() else {
            return result_set;
        };
        let mut min = f(first);
        result_set.insert(first);

        for next in iter {
            let k = f(next);
            match k.cmp(&min) {
                core::cmp::Ordering::Less => {
                    result_set = Self::EMPTY;
                    result_set.insert(next);
                    min = k;
                }
                core::cmp::Ordering::Equal => {
                    result_set.insert(next);
                }
                core::cmp::Ordering::Greater => {}
            }
        }

        result_set
    }

    /// Returns the n+1th element present in the set, if there are at least n + 1 elements
    /// To return the first element, use n == 0
    #[must_use]
    fn nth(&self, n: u32) -> Option<SetElement>;

    /// Returns the number of elements less than `element` in the set
    /// Returns the same result regardless of whether `element` is present
    #[must_use]
    fn count_lesser_elements(&self, element: SetElement) -> u32;

    /// Returns the number of elements greater than `element` in the set
    /// Returns the same result regardless of whether `element` is present
    #[must_use]
    fn count_greater_elements(&self, element: SetElement) -> u32;

    /// Return the smallest element greater than `index`
    /// Will return the same regardless of whether `element` is present
    #[must_use]
    fn smallest_element_greater_than(&self, index: SetElement) -> Option<SetElement>;

    /// Return the smallest element less than `index`
    /// Will return the same regardless of whether `element` is present
    #[must_use]
    fn largest_element_less_than(&self, index: SetElement) -> Option<SetElement>;

    /// Retains only the elements specified by the predicate.     
    fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&SetElement) -> bool,
        Self: Clone,
    {
        //todo specialize this implementation for BitSetVec - no clone needed
        let clone = self.clone();
        let iter = clone.iter();
        for x in iter {
            if f(&x) {
                self.remove(x);
            }
        }
    }

    #[must_use]
    fn iter_subsets(
        self,
        subset_size: u32,
    ) -> impl ExactSizeIterator<Item = Self> + Clone + core::iter::FusedIterator
    where
        Self: Clone,
    {
        crate::subset_iter::SubsetIter::new(self, subset_size)
    }

    #[must_use]
    fn count_subsets(&self, subset_size: u32) -> u32 {
        crate::n_choose_k::NChooseK::new(self.count(), subset_size).value()
    }

    #[must_use]
    fn index_of_subset(&self, subset: &Self) -> u32 {
        let n_c_k = crate::n_choose_k::NChooseK::new(self.count(), subset.count());

        let Some(mut n_c_k) = n_c_k.try_decrement_n() else {
            return 0;
        };

        let mut total = 0;
        let mut iter = self.iter();
        while let Some(index) = iter.next_back() {
            if subset.contains(index) {
                total += n_c_k.value();
                match n_c_k.try_decrement_k() {
                    Some(r) => n_c_k = r,
                    None => return total,
                }
            }
            match n_c_k.try_decrement_n() {
                Some(r) => n_c_k = r,
                None => return total,
            }
        }

        total
    }

    #[must_use]
    fn get_subset(&self, subset_size: u32, index: u32) -> Self {
        let n_c_k = crate::n_choose_k::NChooseK::new(self.count(), subset_size);

        // The rest of this algorithm calculates the the subsets in reverse order (i.e. index 0 is the largest subset)
        // So reverse the order here to account for that
        let mut index = n_c_k.value() - (index + 1 % n_c_k.value());
        let mut new_set = Self::EMPTY;

        let Some(mut n_c_k) = n_c_k.try_decrement_k().and_then(|x| x.try_decrement_n()) else {
            return new_set;
        };

        let mut iter = self.iter();

        while let Some(next) = iter.next_back() {
            if let Some(new_index) = index.checked_sub(n_c_k.value()) {
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
                None => {
                    //todo do union here
                    iter.fold(&mut new_set, |acc, x| {
                        acc.insert(x);
                        acc
                    });

                    return new_set;
                }
            }
        }

        new_set
    }

    ///Returns the number of ones at the beginning of the set
    /// See `FiniteBitSet` for `trailing_zeros`, `leading_ones` and `leading_zeros`
    fn trailing_ones(&self) -> u32;
}

macro_rules! impl_bit_set_trait_methods {
    () => {
        fn is_empty(&self) -> bool {
            self.is_empty_const()
        }

        fn count(&self) -> u32 {
            self.count_const()
        }

        fn clear(&mut self) {
            self.clear_const()
        }

        fn into_inner(self) -> Self::Inner {
            self.into_inner_const()
        }

        fn from_inner(inner: Self::Inner) -> Self {
            Self::from_inner_const(inner)
        }

        fn from_first_n(n: u32) -> Self {
            Self::from_first_n_const(n)
        }

        fn contains(&self, element: SetElement) -> bool {
            self.contains_const(element)
        }

        fn first(&self) -> Option<SetElement> {
            self.first_const()
        }

        fn last(&self) -> Option<SetElement> {
            self.last_const()
        }

        fn pop(&mut self) -> Option<SetElement> {
            self.pop_const()
        }

        fn pop_last(&mut self) -> Option<SetElement> {
            self.pop_last_const()
        }

        fn insert(&mut self, element: SetElement) -> bool {
            self.insert_const(element)
        }

        fn remove(&mut self, element: SetElement) -> bool {
            self.remove_const(element)
        }

        fn swap_bits(&mut self, i: u32, j: u32) {
            self.swap_bits_const(i, j);
        }

        fn is_subset(&self, rhs: &Self) -> bool {
            self.is_subset_const(rhs)
        }

        fn overlaps(&self, rhs: &Self) -> bool {
            self.overlaps_const(rhs)
        }

        fn intersect_with(&mut self, rhs: &Self) {
            self.intersect_with_const(rhs);
        }

        fn union_with(&mut self, rhs: &Self) {
            self.union_with_const(rhs)
        }

        fn except_with(&mut self, rhs: &Self) {
            self.except_with_const(rhs)
        }

        fn symmetric_difference_with(&mut self, rhs: &Self) {
            self.symmetric_difference_with_const(rhs);
        }

        fn nth(&self, n: u32) -> Option<SetElement> {
            self.nth_const(n)
        }

        fn count_lesser_elements(&self, element: SetElement) -> u32 {
            self.count_lesser_elements_const(element)
        }

        fn count_greater_elements(&self, element: SetElement) -> u32 {
            self.count_greater_elements_const(element)
        }

        fn smallest_element_greater_than(&self, index: SetElement) -> Option<SetElement> {
            self.smallest_element_greater_than_const(index)
        }

        fn largest_element_less_than(&self, index: SetElement) -> Option<SetElement> {
            self.largest_element_less_than_const(index)
        }

        fn trailing_ones(&self) -> u32 {
            self.trailing_ones_const()
        }

        fn iter<'a>(
            &'a self,
        ) -> impl Iterator<Item = SetElement>
        + Clone
        + FusedIterator
        + DoubleEndedIterator
        + ExactSizeIterator {
            self.iter_const()
        }
    };
}

macro_rules! impl_bit_set_trait {
    ($name:ident, $inner: ty) => {
        impl BitSet for $name {
            type Inner = $inner;
            const EMPTY: Self = Self::EMPTY;

            impl_bit_set_trait_methods!();
        }
    };
}

impl_bit_set_trait!(BitSet8, u8);
impl_bit_set_trait!(BitSet16, u16);
impl_bit_set_trait!(BitSet32, u32);
impl_bit_set_trait!(BitSet64, u64);
impl_bit_set_trait!(BitSet128, u128);

impl<const WORDS: usize> BitSet for BitSetArray<WORDS> {
    type Inner = [u64; WORDS];
    const EMPTY: Self = Self::EMPTY;

    impl_bit_set_trait_methods!();
}
