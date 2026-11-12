use crate::cmp::Comparator;
#[cfg(test)]
use crate::laws::*;

/// An algorithm is a trait; strategies are unit types. That is what makes it trait-testable.
pub trait Sort {
    fn sort<T, C: Comparator<T>>(s: &mut [T], c: C);
}

/// Marker: the strategy additionally promises stability.
pub trait StableSort: Sort {}

pub struct Insertion;
#[cfg_attr(test, trait_tests::test_impl)]
impl Sort for Insertion {
    fn sort<T, C: Comparator<T>>(s: &mut [T], mut c: C) {
        for i in 1..s.len() {
            let mut j = i;
            while j > 0 && c.lt(&s[j], &s[j - 1]) {
                s.swap(j, j - 1);
                j -= 1;
            }
        }
    }
}
#[cfg_attr(test, trait_tests::test_impl)]
impl StableSort for Insertion {}

/// Lomuto quicksort, not stable, naive pivot.
pub struct Quick;
#[cfg_attr(test, trait_tests::test_impl)]
impl Sort for Quick {
    fn sort<T, C: Comparator<T>>(s: &mut [T], mut c: C) {
        fn go<T, C: Comparator<T>>(s: &mut [T], c: &mut C) {
            if s.len() <= 1 {
                return;
            }
            let last = s.len() - 1;
            let mut store = 0;
            for i in 0..last {
                if c.lt(&s[i], &s[last]) {
                    s.swap(i, store);
                    store += 1;
                }
            }
            s.swap(store, last);
            let (l, r) = s.split_at_mut(store);
            go(l, c);
            go(&mut r[1..], c);
        }
        go(s, &mut c)
    }
}

/// Delegates to std. Only here to show a third implementor.
pub struct Std;
#[cfg_attr(test, trait_tests::test_impl)]
impl Sort for Std {
    fn sort<T, C: Comparator<T>>(s: &mut [T], mut c: C) {
        s.sort_unstable_by(|a, b| c.compare(a, b))
    }
}
