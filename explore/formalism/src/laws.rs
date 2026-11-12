//! Trait-level law suites, shipped so downstream semirings can be checked with
//! `#[cfg_attr(test, test_impl)]`. These are the executable form of the Lean axioms in
//! `verify/`; a semiring with a Lean proof does not need them.
use crate::semiring::{Dioid, Semiring};
use trait_tests::trait_tests;

#[trait_tests]
pub trait SemiringTests: Semiring {
    fn samples() -> [Self; 5] {
        let two = Self::one().add(Self::one());
        let three = two.add(Self::one());
        [Self::zero(), Self::one(), two, three, two.mul(three).add(Self::one())]
    }
    fn zero_ne_one() { assert_ne!(Self::zero(), Self::one()); }
    fn add_identity() {
        for a in Self::samples() { assert_eq!(a.add(Self::zero()), a); assert_eq!(Self::zero().add(a), a); }
    }
    fn mul_identity() {
        for a in Self::samples() { assert_eq!(a.mul(Self::one()), a); assert_eq!(Self::one().mul(a), a); }
    }
    fn zero_annihilates() {
        for a in Self::samples() { assert_eq!(a.mul(Self::zero()), Self::zero()); assert_eq!(Self::zero().mul(a), Self::zero()); }
    }
    fn add_commutative() {
        for a in Self::samples() { for b in Self::samples() { assert_eq!(a.add(b), b.add(a)); } }
    }
    fn mul_commutative() {
        for a in Self::samples() { for b in Self::samples() { assert_eq!(a.mul(b), b.mul(a)); } }
    }
    fn add_associative() {
        for a in Self::samples() { for b in Self::samples() { for c in Self::samples() {
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
            assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)), "{a:?} {b:?} {c:?}");
        } } }
    }
}

#[trait_tests]
pub trait DioidTests: Dioid + SemiringTests {
    fn add_is_min() {
        for a in Self::samples() { for b in Self::samples() {
            let m = a.add(b);
            assert!(m == a || m == b);
            assert!(m.le(a) && m.le(b));
        } }
    }
    fn total_order() {
        for a in Self::samples() { for b in Self::samples() {
            assert!(a.le(b) || b.le(a));
            if a.le(b) && b.le(a) { assert_eq!(a, b); }
        } }
    }
    fn idempotent() { for a in Self::samples() { assert_eq!(a.add(a), a); } }
    fn regular_cancels() {
        for a in Self::samples() { for b in Self::samples() { for c in Self::samples() {
            if a.regular() && a.mul(b) == a.mul(c) { assert_eq!(b, c, "{a:?} {b:?} {c:?}"); }
        } } }
    }
    fn zero_not_regular() { assert!(!Self::zero().regular()); }
}
