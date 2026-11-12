//! Law suites. Each `XTests` trait is the shipped contract for trait `X`.
//! A downstream `impl X for Y` gets the whole suite with `#[cfg_attr(test, test_impl)]`.
extern crate std;
use std::vec::Vec;

use crate::cmp::Comparator;
use crate::search::LowerBound;
use crate::semiring::Semiring;
use crate::sort::{Sort, StableSort};
use core::cmp::Ordering;
use trait_tests::trait_tests;

const SAMPLE: [i32; 7] = [-5, -1, 0, 0, 3, 7, 7];

/// Heap's algorithm: every permutation of `v`, in place.
fn for_each_permutation<T: Clone>(v: &mut [T], f: &mut impl FnMut(&[T])) {
    fn go<T: Clone>(k: usize, v: &mut [T], f: &mut impl FnMut(&[T])) {
        if k <= 1 {
            f(v);
            return;
        }
        go(k - 1, v, f);
        for i in 0..k - 1 {
            if k % 2 == 0 { v.swap(i, k - 1) } else { v.swap(0, k - 1) }
            go(k - 1, v, f);
        }
    }
    go(v.len(), v, f)
}

/// Small exhaustive corpus: every permutation of every prefix of `SAMPLE`.
fn corpus(mut f: impl FnMut(&[i32])) {
    for n in 0..=SAMPLE.len() {
        let mut v: Vec<i32> = SAMPLE[..n].to_vec();
        for_each_permutation(&mut v, &mut f);
    }
}

#[trait_tests]
pub trait ComparatorTests: Comparator<i32> + Default + Sized {
    fn reflexive() {
        let mut c = Self::default();
        for a in SAMPLE { assert_eq!(c.compare(&a, &a), Ordering::Equal); }
    }
    fn antisymmetric() {
        let mut c = Self::default();
        for a in SAMPLE { for b in SAMPLE {
            assert_eq!(c.compare(&a, &b), c.compare(&b, &a).reverse());
        } }
    }
    fn transitive() {
        let mut c = Self::default();
        for a in SAMPLE { for b in SAMPLE { for d in SAMPLE {
            if c.lt(&a, &b) && c.lt(&b, &d) { assert!(c.lt(&a, &d), "{a} {b} {d}"); }
        } } }
    }
    fn lt_consistent_with_compare() {
        let mut c = Self::default();
        for a in SAMPLE { for b in SAMPLE {
            assert_eq!(c.lt(&a, &b), c.compare(&a, &b) == Ordering::Less);
        } }
    }
}

#[trait_tests]
pub trait SemiringTests: Semiring {
    fn samples() -> [Self; 4] {
        let two = Self::one().add(Self::one());
        [Self::zero(), Self::one(), two, two.mul(two).add(Self::one())]
    }
    fn add_identity() {
        for a in Self::samples() { assert_eq!(a.add(Self::zero()), a); assert_eq!(Self::zero().add(a), a); }
    }
    fn mul_identity() {
        for a in Self::samples() { assert_eq!(a.mul(Self::one()), a); assert_eq!(Self::one().mul(a), a); }
    }
    fn zero_annihilates() {
        for a in Self::samples() { assert_eq!(a.mul(Self::zero()), Self::zero()); assert_eq!(Self::zero().mul(a), Self::zero()); }
    }
    fn add_commutative_associative() {
        for a in Self::samples() { for b in Self::samples() { for c in Self::samples() {
            assert_eq!(a.add(b), b.add(a));
            assert_eq!(a.add(b).add(c), a.add(b.add(c)));
        } } }
    }
    fn mul_associative() {
        for a in Self::samples() { for b in Self::samples() { for c in Self::samples() {
            assert_eq!(a.mul(b).mul(c), a.mul(b.mul(c)));
        } } }
    }
    fn distributive() {
        for a in Self::samples() { for b in Self::samples() { for c in Self::samples() {
            assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)), "left {a:?} {b:?} {c:?}");
            assert_eq!(b.add(c).mul(a), b.mul(a).add(c.mul(a)), "right {a:?} {b:?} {c:?}");
        } } }
    }
}

#[trait_tests]
pub trait SortTests: Sort {
    fn output_is_sorted() {
        corpus(|input| {
            let mut v = input.to_vec();
            Self::sort(&mut v, crate::cmp::Natural);
            assert!(v.windows(2).all(|w| w[0] <= w[1]), "{input:?} -> {v:?}");
        });
    }
    fn output_is_permutation_of_input() {
        corpus(|input| {
            let mut v = input.to_vec();
            Self::sort(&mut v, crate::cmp::Natural);
            let mut expect = input.to_vec();
            expect.sort();
            assert_eq!(v, expect);
        });
    }
    fn respects_comparator() {
        corpus(|input| {
            let mut v = input.to_vec();
            Self::sort(&mut v, crate::cmp::Reverse(crate::cmp::Natural));
            assert!(v.windows(2).all(|w| w[0] >= w[1]), "{input:?} -> {v:?}");
        });
    }
}

#[trait_tests]
pub trait StableSortTests: StableSort {
    fn equal_keys_keep_input_order() {
        corpus(|input| {
            let mut v: Vec<(i32, usize)> = input.iter().copied().zip(0..).collect();
            Self::sort(&mut v, crate::cmp::ByKey(|p: &(i32, usize)| p.0));
            assert!(v.windows(2).all(|w| w[0].0 < w[1].0 || w[0].1 < w[1].1), "{input:?} -> {v:?}");
        });
    }
}

#[trait_tests]
pub trait LowerBoundTests: LowerBound {
    fn matches_definition() {
        corpus(|input| {
            let mut s = input.to_vec();
            s.sort();
            for x in -6..9 {
                let got = Self::lower_bound(&s, &x, crate::cmp::Natural);
                let want = s.iter().position(|e| *e >= x).unwrap_or(s.len());
                assert_eq!(got, want, "{s:?} x={x}");
            }
        });
    }
}
