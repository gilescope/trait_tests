//! Join/union expressions (Definitions 7–9) and their linear-time measure (Lemma 1).
use crate::semiring::Semiring;
use alloc::boxed::Box;
use alloc::vec::Vec;

pub type Var = u32;
pub type Val = u32;

/// `E ::= ∅ | T^∅ | (s ↦ t) | E ⊎ E | E ⨝ E`.
///
/// Semantics are sets of partial assignments `Var -> Val`:
/// `Empty` = {}, `Unit` = { the empty assignment }, `Leaf(s,t)` = { {s ↦ t} },
/// `Union` = disjoint set union (same domains), `Join` = pointwise join over disjoint domains.
/// Union over non-disjoint sets or Join over overlapping domains is FAIL; the DP in
/// `scheme` never produces such expressions (that is the correctness theorem).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr {
    Empty,
    Unit,
    Leaf(Var, Val),
    Union(Box<Expr>, Box<Expr>),
    Join(Box<Expr>, Box<Expr>),
}

/// A measure matrix `M[s, t]` into a commutative semiring (Definition 9).
pub trait Measure<A: Semiring> {
    fn weight(&self, s: Var, t: Val) -> A;
}

/// Lemma 1: `eval(E, μ) = μ(⟦E⟧)` in `O(‖E‖)` semiring operations.
pub fn eval<A: Semiring, M: Measure<A>>(e: &Expr, m: &M) -> A {
    match e {
        Expr::Empty => A::zero(),
        Expr::Unit => A::one(),
        Expr::Leaf(s, t) => m.weight(*s, *t),
        Expr::Union(a, b) => eval(a, m).add(eval(b, m)),
        Expr::Join(a, b) => eval(a, m).mul(eval(b, m)),
    }
}

/// Number of leaves, `‖E‖`.
pub fn size(e: &Expr) -> usize {
    match e {
        Expr::Empty | Expr::Unit | Expr::Leaf(_, _) => 1,
        Expr::Union(a, b) | Expr::Join(a, b) => size(a) + size(b),
    }
}

/// `E ⊎ F`, absorbing `∅`.
pub fn union(a: Expr, b: Expr) -> Expr {
    if a == Expr::Empty { return b; }
    if b == Expr::Empty { return a; }
    Expr::Union(Box::new(a), Box::new(b))
}

/// `E ⨝ F`, with `T^∅` as unit and `∅` as zero.
pub fn join(a: Expr, b: Expr) -> Expr {
    if a == Expr::Empty || b == Expr::Empty { return Expr::Empty; }
    if a == Expr::Unit { return b; }
    if b == Expr::Unit { return a; }
    Expr::Join(Box::new(a), Box::new(b))
}

/// `E ⨝ (s1 ↦ t1) ⨝ ... ⨝ (sn ↦ tn)`.
pub fn join_leaves(mut e: Expr, leaves: &[(Var, Val)]) -> Expr {
    let mut i = 0;
    while i < leaves.len() {
        e = join(e, Expr::Leaf(leaves[i].0, leaves[i].1));
        i += 1;
    }
    e
}

/// The measure every semiring `A` induces when every `M[s,t] = 1`:
/// decision for `Boolean`, counting for `Nat`.
pub struct Ones;
impl<A: Semiring> Measure<A> for Ones {
    fn weight(&self, _: Var, _: Val) -> A { A::one() }
}

/// A dense weight table `M[s][t]`, for cost measures.
pub struct Table<A> {
    pub rows: Vec<Vec<A>>,
}
impl<A: Semiring> Measure<A> for Table<A> {
    fn weight(&self, s: Var, t: Val) -> A { self.rows[s as usize][t as usize] }
}

/// Explicit set semantics `⟦E⟧`, for oracles. `None` is FAIL.
/// Assignments are sorted `(Var, Val)` lists; sets are sorted, deduplicated lists.
#[cfg(any(test, feature = "trait-tests"))]
pub mod semantics {
    extern crate std;
    use super::*;
    use std::collections::BTreeSet;

    pub type Assignment = Vec<(Var, Val)>;
    pub type SolutionSet = BTreeSet<Assignment>;

    fn dom(a: &Assignment) -> BTreeSet<Var> { a.iter().map(|p| p.0).collect() }

    pub fn semantics(e: &Expr) -> Option<SolutionSet> {
        match e {
            Expr::Empty => Some(SolutionSet::new()),
            Expr::Unit => Some([Vec::new()].into_iter().collect()),
            Expr::Leaf(s, t) => Some([alloc::vec![(*s, *t)]].into_iter().collect()),
            Expr::Union(a, b) => {
                let (a, b) = (semantics(a)?, semantics(b)?);
                if !a.is_disjoint(&b) { return None; }
                let doms: BTreeSet<BTreeSet<Var>> = a.iter().chain(b.iter()).map(dom).collect();
                if doms.len() > 1 { return None; }
                Some(a.union(&b).cloned().collect())
            }
            Expr::Join(a, b) => {
                let (a, b) = (semantics(a)?, semantics(b)?);
                let mut out = SolutionSet::new();
                for f in &a {
                    for g in &b {
                        if !dom(f).is_disjoint(&dom(g)) { return None; }
                        let mut h = f.clone();
                        h.extend(g.iter().cloned());
                        h.sort();
                        out.insert(h);
                    }
                }
                Some(out)
            }
        }
    }
}
