//! Carriers and their laws. Laws are the contract; see FORMALISM.md for the test/proof story.

/// Commutative semiring. Laws: (add, zero) and (mul, one) commutative monoids, mul distributes, zero absorbs.
pub trait Semiring: Copy + PartialEq + core::fmt::Debug {
    fn zero() -> Self;
    fn one() -> Self;
    fn add(self, o: Self) -> Self;
    fn mul(self, o: Self) -> Self;
}

/// Lehmann: a* = 1 + a·a*. Makes `closure` well defined (Floyd–Warshall, Warshall, Kleene).
pub trait Star: Semiring {
    fn star(self) -> Self;
}

/// Mohri: ⊕ₙ₌₀ᵏ⁺¹ aⁿ = ⊕ₙ₌₀ᵏ aⁿ. Makes `relax` terminate with the right answer for any queue.
/// K = 0 is "bounded" (1 ⊕ a = 1), which implies idempotent.
pub trait KClosed<const K: usize>: Semiring {}

/// Huang: a ≤ a⊗b and b ≤ a⊗b in the natural order. Makes shortest-first pop each node once.
pub trait Superior: Semiring + PartialOrd {}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
pub struct Boolean(pub bool);
impl Semiring for Boolean {
    fn zero() -> Self { Boolean(false) }
    fn one() -> Self { Boolean(true) }
    fn add(self, o: Self) -> Self { Boolean(self.0 || o.0) }
    fn mul(self, o: Self) -> Self { Boolean(self.0 && o.0) }
}
impl Star for Boolean { fn star(self) -> Self { Boolean(true) } }
impl KClosed<0> for Boolean {}

/// Counting in Z/2^64. Not idempotent: `relax` must use Mohri's r[q] accumulator, and is only
/// k-closed on acyclic graphs, so it carries no `KClosed` impl; `relax` on a DAG is `relax_acyclic`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Nat(pub u64);
impl Semiring for Nat {
    fn zero() -> Self { Nat(0) }
    fn one() -> Self { Nat(1) }
    fn add(self, o: Self) -> Self { Nat(self.0.wrapping_add(o.0)) }
    fn mul(self, o: Self) -> Self { Nat(self.0.wrapping_mul(o.0)) }
}

/// (min, +) with u64::MAX as ∞.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Tropical(pub u64);
impl Tropical { pub const INF: Tropical = Tropical(u64::MAX); }
impl Default for Tropical { fn default() -> Self { Tropical::INF } }
impl Semiring for Tropical {
    fn zero() -> Self { Tropical::INF }
    fn one() -> Self { Tropical(0) }
    fn add(self, o: Self) -> Self { if self.0 <= o.0 { self } else { o } }
    fn mul(self, o: Self) -> Self { if self.0 == u64::MAX || o.0 == u64::MAX { Tropical::INF } else { Tropical(self.0 + o.0) } }
}
impl Star for Tropical { fn star(self) -> Self { Tropical(0) } }
/// 0-closed only without negative cycles; u64 weights have none.
impl KClosed<0> for Tropical {}
impl Superior for Tropical {}
