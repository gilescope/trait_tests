#[cfg(test)]
use crate::laws::*;

pub trait Semiring: Copy + PartialEq + core::fmt::Debug {
    fn zero() -> Self;
    fn one() -> Self;
    fn add(self, o: Self) -> Self;
    fn mul(self, o: Self) -> Self;
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

/// (min, +): optimum. `u64::MAX` is "infinity".
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Tropical(pub u64);
#[cfg_attr(test, trait_tests::test_impl)]
impl Semiring for Tropical {
    fn zero() -> Self { Tropical(u64::MAX) }
    fn one() -> Self { Tropical(0) }
    fn add(self, o: Self) -> Self { Tropical(self.0.min(o.0)) }
    fn mul(self, o: Self) -> Self { Tropical(self.0.saturating_add(o.0)) }
}

/// (+, *) mod 2^64: counting.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Count(pub u64);
#[cfg_attr(test, trait_tests::test_impl)]
impl Semiring for Count {
    fn zero() -> Self { Count(0) }
    fn one() -> Self { Count(1) }
    fn add(self, o: Self) -> Self { Count(self.0.wrapping_add(o.0)) }
    fn mul(self, o: Self) -> Self { Count(self.0.wrapping_mul(o.0)) }
}

/// Deliberately wrong: `mul` is not distributive over `add`. Exists to prove the laws catch it;
/// see the `should_panic` tests below rather than `#[test_impl]`, so CI stays green.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Broken(pub u64);
impl Semiring for Broken {
    fn zero() -> Self { Broken(0) }
    fn one() -> Self { Broken(1) }
    fn add(self, o: Self) -> Self { Broken(self.0.wrapping_add(o.0)) }
    fn mul(self, o: Self) -> Self { Broken(self.0.max(o.0)) }
}

#[cfg(test)]
mod broken_is_caught {
    use super::*;
    impl SemiringTests for Broken {}
    #[test] #[should_panic] fn distributive() { <Broken as SemiringTests>::distributive() }
    #[test] #[should_panic] fn mul_identity() { <Broken as SemiringTests>::mul_identity() }
    #[test] #[should_panic] fn zero_annihilates() { <Broken as SemiringTests>::zero_annihilates() }
}
