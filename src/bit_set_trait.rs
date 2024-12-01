use crate::{BitSet16, SetElement};

pub trait BitSetTrait:
    core::fmt::Debug
    + Clone
    + Copy
    + PartialEq
    + Eq
    + Ord
    + PartialOrd
    + Default
    + Extend<SetElement>
    + FromIterator<SetElement>
    + IntoIterator<Item = SetElement>
{
    type Inner;

    const EMPTY: Self;
    const ALL: Self;
    const MAX_COUNT: u32;

    #[doc(alias = "count")]
    fn len(&self) -> u32;

    fn inner(self) -> Self::Inner;
    fn from_inner(inner: Self::Inner) -> Self;

    fn from_first_n(n: u32) -> Self;

    fn from_fn<F: FnMut(SetElement) -> bool>(mut f: F) -> Self {
        let mut result = Self::EMPTY;
        for x in (0..(Self::MAX_COUNT)).filter(|x| f(*x)) {
            result.insert(x);
        }

        result
    }

    fn is_empty(self) -> bool {
        self == Self::EMPTY
    }

    fn contains(&self, element: SetElement) -> bool;

    #[doc(alias = "min")]
    fn first(&self) -> Option<SetElement>;

    #[doc(alias = "max")]
    fn last(&self) -> Option<SetElement>;

    fn pop(&mut self) -> Option<SetElement>;

    fn pop_last(&mut self) -> Option<SetElement>;

    /// Sets the `element` to `bit`.
    /// Returns whether the element was changed
    fn set_bit(&mut self, element: SetElement, bit: bool) -> bool {
        if bit {
            self.insert(element)
        } else {
            self.remove(element)
        }
    }
    fn with_bit_set(&self, element: SetElement, bit: bool) -> Self {
        let mut s = *self;
        s.set_bit(element, bit);
        s
    }

    fn insert(&mut self, element: SetElement) -> bool;
    fn with_inserted(&self, element: SetElement) -> Self {
        let mut s = *self;
        s.insert(element);
        s
    }

    fn remove(&mut self, element: SetElement) -> bool;
    fn with_removed(&self, element: SetElement) -> Self {
        let mut s = *self;
        s.remove(element);
        s
    }

    fn swap_bits(&mut self, i: u32, j: u32);
    fn with_bits_swapped(&self, i: u32, j: u32) -> Self {
        let mut s = *self;
        s.swap_bits(i, j);
        s
    }

    fn is_subset(&self, rhs: &Self) -> bool;
    fn is_superset(&self, rhs: &Self) -> bool {
        rhs.is_subset(self)
    }
    fn overlaps(&self, rhs: &Self) -> bool;

    fn intersect_with(&mut self, rhs: &Self);
    fn with_intersect(&self, rhs: &Self) -> Self {
        let mut s = *self;
        s.intersect_with(rhs);
        s
    }

    fn union_with(&mut self, rhs: &Self);
    fn with_union(&self, rhs: &Self) -> Self {
        let mut s = *self;
        s.union_with(rhs);
        s
    }

    fn except_with(&mut self, rhs: &Self);
    fn with_except(&self, rhs: &Self) -> Self {
        let mut s = *self;
        s.except_with(rhs);
        s
    }

    fn symmetric_difference_with(&mut self, rhs: &Self);
    fn with_symmetric_difference(&self, rhs: &Self) -> Self {
        let mut s = *self;
        s.symmetric_difference_with(rhs);
        s
    }

    fn negate(&mut self);
    fn with_negated(&self) -> Self {
        let mut s = *self;
        s.negate();
        s
    }

    /// Return the set of minimal members according to a function#
    #[must_use]
    fn min_set_by_key<K: Ord>(&self, f: impl Fn(SetElement) -> K) -> Self {
        let mut result_set = Self::EMPTY;
        let mut s = *self;

        let Some(first) = s.pop() else {
            return result_set;
        };
        let mut min = f(first);
        result_set.insert(first);

        while let Some(next) = s.pop() {
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

        return result_set;
    }
}

impl BitSetTrait for BitSet16 {
    type Inner = u16;

    const EMPTY: Self = Self::EMPTY;

    const ALL: Self = Self::ALL;

    const MAX_COUNT: u32 = Self::MAX_COUNT;

    fn len(&self) -> u32 {
        self.len_const()
    }

    fn inner(self) -> Self::Inner {
        self.inner_const()
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

    fn symmetric_difference_with(&mut self, rhs: &Self){
        self.symmetric_difference_with_const(rhs);
    }

    fn negate(&mut self) {
        self.negate_const();
    }
}
