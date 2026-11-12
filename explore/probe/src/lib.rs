//! The bare core of `hylo`, with no collections: Option-shaped layers only.
//! If this extracts, the GAT is fine and any later failure is a missing std model.
#![no_std]

pub trait Shape {
    type Layer<X>;
    fn map<A, B>(layer: Self::Layer<A>, f: impl FnMut(A) -> B) -> Self::Layer<B>;
}
pub trait Plan<S: Shape> {
    type Seed;
    fn unfold(&mut self, seed: Self::Seed) -> S::Layer<Self::Seed>;
}
pub trait Algebra<S: Shape> {
    type Out;
    fn fold(&mut self, layer: S::Layer<Self::Out>) -> Self::Out;
}
pub fn hylo<S: Shape, P: Plan<S>, A: Algebra<S>>(plan: &mut P, alg: &mut A, seed: P::Seed) -> A::Out {
    let layer = plan.unfold(seed);
    let folded = S::map(layer, |x| hylo::<S, P, A>(plan, alg, x));
    alg.fold(folded)
}

/// Nil | Cons(head, rest), with the head a `u32`.
pub struct ListF;
impl Shape for ListF {
    type Layer<X> = Option<(u32, X)>;
    fn map<A, B>(l: Option<(u32, A)>, mut f: impl FnMut(A) -> B) -> Option<(u32, B)> {
        match l { None => None, Some((h, x)) => Some((h, f(x))) }
    }
}

/// Count down from `n`: the simplest recursive plan.
pub struct CountDown;
impl Plan<ListF> for CountDown {
    type Seed = u32;
    fn unfold(&mut self, n: u32) -> Option<(u32, u32)> { if n == 0 { None } else { Some((n, n - 1)) } }
}

/// Sum the heads.
pub struct Sum;
impl Algebra<ListF> for Sum {
    type Out = u32;
    fn fold(&mut self, l: Option<(u32, u32)>) -> u32 { match l { None => 0, Some((h, t)) => h + t } }
}

/// 1 + 2 + ... + n. The theorem to prove on the Lean side: `triangle n = n * (n + 1) / 2`,
/// or `fail` on overflow, which is what Aeneas's `Result` is for.
pub fn triangle(n: u32) -> u32 { hylo::<ListF, _, _>(&mut CountDown, &mut Sum, n) }

#[cfg(test)]
mod t {
    #[test]
    fn triangle_numbers() { assert_eq!((0..6).map(super::triangle).collect::<alloc::vec::Vec<_>>(), [0, 1, 3, 6, 10, 15]); }
    extern crate alloc;
}
