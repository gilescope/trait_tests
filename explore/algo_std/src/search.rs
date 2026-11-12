use crate::cmp::Comparator;
#[cfg(test)]
use crate::laws::*;

/// Contract: `s` sorted under `c`; returns first index `i` with `!(s[i] < x)`.
pub trait LowerBound {
    fn lower_bound<T, C: Comparator<T>>(s: &[T], x: &T, c: C) -> usize;
}

pub struct Linear;
#[cfg_attr(test, trait_tests::test_impl)]
impl LowerBound for Linear {
    fn lower_bound<T, C: Comparator<T>>(s: &[T], x: &T, mut c: C) -> usize {
        s.iter().position(|e| !c.lt(e, x)).unwrap_or(s.len())
    }
}

pub struct Binary;
#[cfg_attr(test, trait_tests::test_impl)]
impl LowerBound for Binary {
    fn lower_bound<T, C: Comparator<T>>(s: &[T], x: &T, mut c: C) -> usize {
        let (mut lo, mut hi) = (0, s.len());
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if c.lt(&s[mid], x) {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        lo
    }
}

/// Variant with an off-by-one bug. Exists to prove the contract test catches it;
/// see the `should_panic` test below rather than `#[test_impl]`, so CI stays green.
pub struct Buggy;
impl LowerBound for Buggy {
    fn lower_bound<T, C: Comparator<T>>(s: &[T], x: &T, mut c: C) -> usize {
        let (mut lo, mut hi) = (0, s.len());
        while lo < hi {
            let mid = (lo + hi) / 2;
            if c.lt(&s[mid], x) {
                lo = mid + 1;
            } else {
                hi = mid.saturating_sub(1); // bug
            }
        }
        lo
    }
}

#[cfg(test)]
mod buggy_is_caught {
    use super::*;
    impl LowerBoundTests for Buggy {}
    #[test] #[should_panic] fn matches_definition() { <Buggy as LowerBoundTests>::matches_definition() }
}
