#[derive(Debug, Clone, PartialEq)]
pub(crate) struct NChooseK {
    n: u32,
    k: u32,
    value: u32,
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
        prelude::{BitSet, BitSet16, BitSet32},
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
            let expected = superset.get_subset(3, index as u32);

            assert_eq!(subset, expected);
        }
    }

    #[test]
    pub fn test_subset_index_round_trip() {
        let superset = BitSet16::from_fn(|x| x % 2 == 0);
        for subset_size in 0..=8 {
            let n = superset.count_subsets(subset_size);
            for index in 0..n {
                let subset = superset.get_subset(subset_size, index);
                let subset_index = superset.index_of_subset(&subset);
                assert_eq!(index, subset_index);
            }
        }
    }
}
