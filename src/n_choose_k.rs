use crate::prelude::BitSet;

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct NChooseK {
    n: u32,
    k: u32,
    value: u32,
}

pub(crate) fn subsets_count(set: &impl BitSet, subset_size: u32) -> u32 {
    NChooseK::new(set.len(), subset_size).value
}

// pub (crate) fn get_subset_index<B: BitSet + Clone>(superset: &B, subset: &B) -> u32{
//     let mut canonical_set = B::EMPTY;
//     let mut superset = superset.clone();
//     let mut index = 0;
//     while let Some(x) = superset.pop(){
//         if subset.contains(x){
//             canonical_set.insert(index);
//         }
//         index += 1;

//     }

//     panic!()
// }

pub(crate) fn get_subset_index<B: BitSet>(superset: B, subset: &B) -> u32 {
    let n_c_k = crate::n_choose_k::NChooseK::new(superset.len(), subset.len());

    let Some(mut n_c_k) = n_c_k.try_decrement_n() else {
        return 0;
    };

    let mut total = 0;

    //todo use iter() to remove clone requirement
    let mut ss = superset;
    while let Some(index) = ss.pop_last() {
        if subset.contains(index) {
            total += n_c_k.value;
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

pub(crate) fn subset_index_to_member<B: BitSet>(superset: B, subset_size: u32, index: u32) -> B {
    let n_c_k = crate::n_choose_k::NChooseK::new(superset.len(), subset_size);

    // The rest of this algorithm calculates the the subsets in reverse order (i.e. index 0 is the largest subset)
    // So reverse the order here to account for that
    let mut index = n_c_k.value - (index + 1 % n_c_k.value);
    let mut new_set = B::EMPTY;

    let Some(mut n_c_k) = n_c_k.try_decrement_k().and_then(|x| x.try_decrement_n()) else {
        return new_set;
    };

    let mut set_remaining = superset;

    while let Some(next) = set_remaining.pop_last() {
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
                new_set.union_with(&set_remaining);
                return new_set;
            }
        }
    }

    new_set
}

impl NChooseK {
    #[inline]
    pub const fn new(n: u32, k: u32) -> Self {
        let mut result = 1;
        let end = if k < n - k { k } else { n - k };
        let mut i = 0;
        while i < end {
            result *= n - i;
            result /= i + 1;
            i += 1;
        }

        Self {
            n,
            k,
            value: result,
        }
    }
    #[inline]
    pub const fn value(&self) -> u32 {
        self.value
    }

    #[must_use]
    #[inline]
    pub const fn try_decrement_k(&self) -> Option<Self> {
        // when you change k - multiply by k then divide by n - new_k
        let Some(new_k) = self.k.checked_sub(1) else {
            return None;
        };

        let Some(denominator) = self.n.checked_sub(new_k) else {
            return None;
        };
        if denominator == 0 {
            return None;
        }

        let new_result = (self.value * self.k) / denominator;
        Some(Self {
            n: self.n,
            k: new_k,
            value: new_result,
        })
    }

    #[must_use]
    #[inline]
    pub const fn try_decrement_n(&self) -> Option<Self> {
        // to decrease n by 1 - multiply by (n - k) then divide by n
        let Some(new_n) = self.n.checked_sub(1) else {
            return None;
        };
        let Some(n_minus_k) = self.n.checked_sub(self.k) else {
            return None;
        };
        let new_result = (self.value * n_minus_k) / (self.n);
        Some(Self {
            n: new_n,
            k: self.k,
            value: new_result,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        finite::FiniteBitSet,
        prelude::{BitSet16, BitSet32},
    };

    use super::*;

    #[test]
    pub fn test_n_choose_k_dec_n() {
        for n in 2..7 {
            for k in 0..n {
                let n_c_k = NChooseK::new(n, k).try_decrement_n().unwrap();

                let expected = NChooseK::new(n - 1, k).value;
                assert_eq!(n_c_k.value, expected);
            }
        }
    }

    #[test]
    pub fn test_n_choose_k_dec_k() {
        for n in 2..7 {
            for k in 1..=n {
                let n_c_k = NChooseK::new(n, k).try_decrement_k().unwrap();

                let expected = NChooseK::new(n, k - 1).value;
                assert_eq!(n_c_k.value, expected, "n: {n}, old_k: {k}");
            }
        }
    }

    #[test]
    pub fn test_all_subsets() {
        let superset = BitSet32::from_fn(|x| x % 2 == 0);

        for (index, subset) in superset.iter_subsets(3).enumerate() {
            let expected = subset_index_to_member(superset, 3, index as u32);

            assert_eq!(subset, expected)
        }
    }

    #[test]
    pub fn test_subset_index_round_trip() {
        let superset = BitSet16::from_fn(|x| x % 2 == 0);
        for subset_size in 0..=8 {
            let n = subsets_count(&superset, subset_size);
            for index in 0..n {
                let subset = subset_index_to_member(superset, subset_size, index);
                let subset_index = get_subset_index(superset, &subset);
                assert_eq!(index, subset_index)
            }
        }
    }
}
