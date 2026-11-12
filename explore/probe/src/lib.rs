//! The hylo scheme for one fixed shape, written so Aeneas can translate it today:
//! no generic associated type, no closure. The list layer `Option<(u32, X)>` is spelled out.
//! If this extracts, the per-shape form is the verified core and the GAT form is the Rust API.
#![no_std]

/// c : Seed → Option<(u32, Seed)>, must be recursive.
pub trait Plan {
    type Seed;
    fn unfold(&mut self, seed: Self::Seed) -> Option<(u32, Self::Seed)>;
}
/// a : Option<(u32, Out)> → Out.
pub trait Algebra {
    type Out;
    fn fold(&mut self, layer: Option<(u32, Self::Out)>) -> Self::Out;
}

/// hylo(a, c) for the list shape. The recursion is direct, not through `map` and a closure.
pub fn hylo<P: Plan, A: Algebra>(plan: &mut P, alg: &mut A, seed: P::Seed) -> A::Out {
    match plan.unfold(seed) {
        None => alg.fold(None),
        Some((h, next)) => {
            let r = hylo(plan, alg, next);
            alg.fold(Some((h, r)))
        }
    }
}

/// Count down from `n`: the simplest recursive plan.
pub struct CountDown;
impl Plan for CountDown {
    type Seed = u32;
    fn unfold(&mut self, n: u32) -> Option<(u32, u32)> { if n == 0 { None } else { Some((n, n - 1)) } }
}

/// Sum the heads.
pub struct Sum;
impl Algebra for Sum {
    type Out = u32;
    fn fold(&mut self, l: Option<(u32, u32)>) -> u32 { match l { None => 0, Some((h, t)) => h + t } }
}

/// 1 + 2 + ... + n. Lean obligation: `triangle n = n * (n + 1) / 2` or `fail` on overflow.
pub fn triangle(n: u32) -> u32 { hylo(&mut CountDown, &mut Sum, n) }

#[cfg(test)]
mod t {
    extern crate alloc;
    #[test]
    fn triangle_numbers() { assert_eq!((0..6).map(super::triangle).collect::<alloc::vec::Vec<_>>(), [0, 1, 3, 6, 10, 15]); }
}
