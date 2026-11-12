//! Commutative semirings (Definition 3), dioids (Definition 4) and the Δ-product (Section 4).
#[cfg(test)]
use crate::laws::*;

/// Commutative semiring: `(A, add, zero)` commutative monoid, `(A, mul, one)` commutative
/// monoid, `mul` distributes over `add`, `zero` absorbs under `mul`, `zero != one`.
/// No idempotence is assumed.
pub trait Semiring: Copy + PartialEq + core::fmt::Debug {
    fn zero() -> Self;
    fn one() -> Self;
    fn add(self, o: Self) -> Self;
    fn mul(self, o: Self) -> Self;
}

/// Idempotent, totally ordered semiring whose `add` is `min` under `le`.
/// `regular` is multiplicative regularity: `a*b == a*c  ==>  b == c`.
pub trait Dioid: Semiring {
    fn le(self, o: Self) -> bool;
    fn regular(self) -> bool;
}

/// (||, &&): decision.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Boolean(pub bool);

#[cfg_attr(test, trait_tests::test_impl)]
impl Semiring for Boolean {
    fn zero() -> Self { Boolean(false) }
    fn one() -> Self { Boolean(true) }
    fn add(self, o: Self) -> Self { Boolean(self.0 || o.0) }
    fn mul(self, o: Self) -> Self { Boolean(self.0 && o.0) }
}

#[cfg_attr(test, trait_tests::test_impl)]
impl Dioid for Boolean {
    // true is the "small" element: min(true, false) = true = add.
    fn le(self, o: Self) -> bool { self.0 || !o.0 }
    fn regular(self) -> bool { self.0 }
}

/// (+, *) in Z/2^64: counting. Wrapping arithmetic keeps every law exact.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Nat(pub u64);

#[cfg_attr(test, trait_tests::test_impl)]
impl Semiring for Nat {
    fn zero() -> Self { Nat(0) }
    fn one() -> Self { Nat(1) }
    fn add(self, o: Self) -> Self { Nat(self.0.wrapping_add(o.0)) }
    fn mul(self, o: Self) -> Self { Nat(self.0.wrapping_mul(o.0)) }
}

/// (min, +) over u64 ∪ {∞}: minimum cost. `u64::MAX` is ∞.
/// Finite sums that would reach `u64::MAX` panic; Aeneas models that as `fail`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Tropical(pub u64);

impl Tropical {
    pub const INF: Tropical = Tropical(u64::MAX);
}

impl Default for Tropical {
    fn default() -> Self { Tropical::INF }
}

#[cfg_attr(test, trait_tests::test_impl)]
impl Semiring for Tropical {
    fn zero() -> Self { Tropical::INF }
    fn one() -> Self { Tropical(0) }
    fn add(self, o: Self) -> Self { if self.0 <= o.0 { self } else { o } }
    fn mul(self, o: Self) -> Self {
        if self.0 == u64::MAX || o.0 == u64::MAX {
            return Tropical::INF;
        }
        let s = self.0 + o.0; // overflow panics in debug; see doc
        if s == u64::MAX { panic!("Tropical: finite sum reached INF") }
        Tropical(s)
    }
}

#[cfg_attr(test, trait_tests::test_impl)]
impl Dioid for Tropical {
    fn le(self, o: Self) -> bool { self.0 <= o.0 }
    fn regular(self) -> bool { self.0 != u64::MAX }
}

/// The Δ-product `D Δ A` (Definition 12): pairs `(d, a)` with `d` regular or `a == 0`.
/// `add` keeps the `D`-minimum and the `A`-value of the argmin (summing on ties);
/// `mul` is componentwise. `Delta<Tropical, Nat>` counts minimum-cost solutions (Theorem 6).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Delta<D: Dioid, A: Semiring> {
    d: D,
    a: A,
}

impl<D: Dioid, A: Semiring> Delta<D, A> {
    /// Smart constructor: the Δ-set invariant holds by construction.
    pub fn new(d: D, a: A) -> Self {
        if d.regular() { Delta { d, a } } else { Delta { d, a: A::zero() } }
    }
    pub fn cost(self) -> D { self.d }
    pub fn count(self) -> A { self.a }
}

impl<D: Dioid + Default, A: Semiring + Default> Default for Delta<D, A> {
    fn default() -> Self { Delta::new(D::default(), A::default()) }
}

impl<D: Dioid, A: Semiring> Semiring for Delta<D, A> {
    fn zero() -> Self { Delta::new(D::zero(), A::zero()) }
    fn one() -> Self { Delta::new(D::one(), A::one()) }
    fn add(self, o: Self) -> Self {
        if self.d == o.d {
            Delta::new(self.d, self.a.add(o.a))
        } else if self.d.le(o.d) {
            self
        } else {
            o
        }
    }
    fn mul(self, o: Self) -> Self { Delta::new(self.d.mul(o.d), self.a.mul(o.a)) }
}

/// `D1 Δ D2` is again a dioid, lexicographically ordered (Theorem 4).
impl<D1: Dioid, D2: Dioid> Dioid for Delta<D1, D2> {
    fn le(self, o: Self) -> bool {
        if self.d == o.d { self.a.le(o.a) } else { self.d.le(o.d) }
    }
    fn regular(self) -> bool { self.d.regular() && self.a.regular() }
}

// Concrete Δ instances get the full law suites. `#[test_impl]` cannot name a concrete
// type for a generic impl, so these are the two lines it would have generated.
#[cfg(test)]
mod delta_laws {
    use super::*;
    impl SemiringTests for Delta<Tropical, Nat> {}
    impl SemiringTests for Delta<Boolean, Boolean> {}
    impl SemiringTests for Delta<Tropical, Tropical> {}
    impl DioidTests for Delta<Boolean, Boolean> {}
    impl DioidTests for Delta<Tropical, Tropical> {}
    mod tropical_nat { use super::*; SemiringTests!(Delta<Tropical, Nat>); }
    mod trilean { use super::*; SemiringTests!(Delta<Boolean, Boolean>); }
    mod trilean_dioid { use super::*; DioidTests!(Delta<Boolean, Boolean>); }
    mod lex_dioid { use super::*; DioidTests!(Delta<Tropical, Tropical>); }
}
