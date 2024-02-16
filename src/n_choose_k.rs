#[derive(Debug, Clone, PartialEq)]
pub (crate) struct NChooseK {
    n: u32,
    k: u32,
    result: u32,
}

pub fn n_choose_k(n: u32, k: u32) -> u32 {
    let mut result = 1;
    for i in 0..(k.min(n - k)) {
        result *= (n - i);
        result /= (i + 1);
    }

    result
}

impl NChooseK {
    #[must_use]
    pub fn try_decrement_k(&self) -> Option<Self> {
        //todo make try
        // when you change k - multiply by k then divide by n - new_k
        let new = self.clone();
        let new_k = self.k.checked_sub(1)?;

        let new_result = (self.result * self.k) / (self.n - new_k);
        Some(Self {
            n: self.n,
            k: new_k,
            result: new_result,
        })
    }

    #[must_use]
    pub fn try_decrement_n(&self) -> Option<Self> {
        // to decrease n by 1 - multiply by (n - k) then divide by n
        let new_n = self.n.checked_sub(1)?;
        let n_minus_k = self.n.checked_sub(self.k)?;
        let new_result = (self.result * n_minus_k) / (self.n);
        Some(Self {
            n: new_n,
            k: self.k,
            result: new_result,
        })
    }
}

impl NChooseK {
    pub fn new(n: u32, k: u32, result: u32) -> Self {
        debug_assert_eq!(result, n_choose_k(n, k));
        Self { n, k, result }
    }

    pub fn n(&self) -> u32 {
        self.n
    }

    pub fn k(&self) -> u32 {
        self.k
    }

    pub fn result(&self) -> u32 {
        self.result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn test_n_choose_k_dec_n() {
        for n in 2..7 {
            for k in 0..n {
                let result = n_choose_k(n, k);
                let n_c_k = NChooseK::new(n, k, result).try_decrement_n().unwrap();

                let expected = n_choose_k(n - 1, k);
                assert_eq!(n_c_k.result, expected);
            }
        }
    }

    #[test]
    pub fn test_n_choose_k_dec_k() {
        for n in 2..7 {
            for k in 1..=n {
                let result = n_choose_k(n, k);
                let n_c_k = NChooseK::new(n, k, result).try_decrement_k().unwrap();

                let expected = n_choose_k(n, k - 1);
                assert_eq!(n_c_k.result, expected, "n: {n}, old_k: {k}");
            }
        }
    }
}
