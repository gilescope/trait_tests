//! Carriers and their laws. Laws are the contract; see FORMALISM.md for the test/proof story.

// One set of carriers: the semiring hierarchy and the Δ-product live in `formalism::semiring`.
pub use formalism::semiring::{Boolean, Delta, Dioid, MaxPlus, Nat, Semiring, Tropical};

/// Lehmann: a* = 1 + a·a*. Makes `closure` well defined (Floyd–Warshall, Warshall, Kleene).
pub trait Star: Semiring {
    fn star(self) -> Self;
}

/// Mohri: ⊕ₙ₌₀ᵏ⁺¹ aⁿ = ⊕ₙ₌₀ᵏ aⁿ. Makes `relax` terminate with the right answer for any queue.
/// K = 0 is "bounded" (1 ⊕ a = 1), which implies idempotent.
pub trait KClosed<const K: usize>: Semiring {}

/// Huang: a ≤ a⊗b and b ≤ a⊗b in the natural order. Makes shortest-first pop each node once.
pub trait Superior: Semiring + PartialOrd {}

impl Star for Boolean { fn star(self) -> Self { Boolean(true) } }
impl KClosed<0> for Boolean {}

// `Nat` is not idempotent and only k-closed on acyclic graphs: no `KClosed` impl on purpose.

impl Star for Tropical { fn star(self) -> Self { Tropical(0) } }
/// 0-closed only without negative cycles; u64 weights have none.
impl KClosed<0> for Tropical {}
impl Superior for Tropical {}

/// Associative binary operation. The hypothesis of the third homomorphism theorem:
/// with it, any split of a sequence (plan) gives the same reduce.
pub trait Semigroup: Copy { fn op(self, o: Self) -> Self; }
pub trait Monoid: Semigroup { fn unit() -> Self; }

#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Sum(pub u64);
impl Semigroup for Sum { fn op(self, o: Self) -> Self { Sum(self.0.wrapping_add(o.0)) } }
impl Monoid for Sum { fn unit() -> Self { Sum(0) } }

/// 2×2 matrices over Z/2^64 under multiplication: Fibonacci by repeated squaring (FM2GP §7.7).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Mat2(pub [[u64; 2]; 2]);
impl Semigroup for Mat2 {
    fn op(self, o: Self) -> Self {
        let (a, b) = (self.0, o.0);
        let m = |i: usize, j: usize| a[i][0].wrapping_mul(b[0][j]).wrapping_add(a[i][1].wrapping_mul(b[1][j]));
        Mat2([[m(0, 0), m(0, 1)], [m(1, 0), m(1, 1)]])
    }
}
impl Monoid for Mat2 { fn unit() -> Self { Mat2([[1, 0], [0, 1]]) } }

/// Euclidean division, enough for Euclid's algorithm (EoP §5.4 asks for more; this is the minimum).
pub trait Euclidean: Copy + PartialEq {
    fn zero() -> Self;
    fn rem(self, o: Self) -> Self;
}
impl Euclidean for u64 { fn zero() -> Self { 0 } fn rem(self, o: Self) -> Self { self % o } }
