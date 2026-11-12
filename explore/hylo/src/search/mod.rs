//! Knuth 7.2.2 / 7.8: Smith's global search theory as a plan over `RoseF`.
//!
//! GS0  initial(x) describes every solution.   GS1  split only shrinks a space.
//! GS2  every solution passes `filter` (a necessary condition).   GS3  extract is complete.
//! The theorem (Smith & Lowry 4.1): with any necessary filter, the search is correct.
//! The query is a semiring fold over the search tree: Boolean = exists, Nat = count.
use crate::algebra::Semiring;
use crate::shape::RoseF;
use crate::{hylo, Algebra, Plan};
use alloc::vec::Vec;

pub trait GlobalSearch {
    type Input;
    type Space: Clone;
    fn initial(&self, x: &Self::Input) -> Self::Space;
    fn split(&self, r: &Self::Space) -> Vec<Self::Space>;
    /// Necessary condition: false means no solution lives in `r`.
    fn filter(&self, r: &Self::Space) -> bool;
    /// `true` if `r` is itself a solution.
    fn extract(&self, r: &Self::Space) -> bool;
}

/// The plan: unfold a space into its filtered children. Recursive because GS1 makes spaces shrink.
pub struct Backtrack<'p, P: GlobalSearch> { p: &'p P }
impl<'p, P: GlobalSearch> Plan<RoseF<P::Space>> for Backtrack<'p, P> {
    type Seed = P::Space;
    fn unfold(&mut self, r: P::Space) -> (P::Space, Vec<P::Space>) {
        let kids = self.p.split(&r).into_iter().filter(|c| self.p.filter(c)).collect();
        (r, kids)
    }
}

/// The query: a semiring over the search tree. Leaves that extract weigh `one`.
pub struct Aggregate<'p, P: GlobalSearch, S> { p: &'p P, _s: core::marker::PhantomData<S> }
impl<'p, P: GlobalSearch, S: Semiring> Algebra<RoseF<P::Space>> for Aggregate<'p, P, S> {
    type Out = S;
    fn fold(&mut self, (r, kids): (P::Space, Vec<S>)) -> S {
        let here = if self.p.extract(&r) { S::one() } else { S::zero() };
        kids.into_iter().fold(here, S::add)
    }
}

pub fn search<P: GlobalSearch, S: Semiring>(p: &P, x: &P::Input) -> S {
    let root = p.initial(x);
    hylo::<RoseF<P::Space>, _, _>(&mut Backtrack { p }, &mut Aggregate { p, _s: core::marker::PhantomData }, root)
}

/// N-queens: a space is a partial placement, one queen per row so far.
pub struct Queens;
impl GlobalSearch for Queens {
    type Input = usize;
    type Space = (usize, Vec<usize>); // (n, columns by row)
    fn initial(&self, n: &usize) -> Self::Space { (*n, Vec::new()) }
    fn split(&self, (n, cols): &Self::Space) -> Vec<Self::Space> {
        if cols.len() == *n { return Vec::new(); }
        (0..*n).map(|c| { let mut v = cols.clone(); v.push(c); (*n, v) }).collect()
    }
    fn filter(&self, (_, cols): &Self::Space) -> bool {
        let Some((&c, rest)) = cols.split_last() else { return true };
        let r = rest.len();
        rest.iter().enumerate().all(|(i, &ci)| ci != c && (r - i) != c.abs_diff(ci))
    }
    fn extract(&self, (n, cols): &Self::Space) -> bool { cols.len() == *n }
}

// ---- Knuth 7.8: branch and bound. Same shape, same split; the incumbent is plan state.
// The answer is order-independent (it is a max), the cost is not: that is exactly what
// the Plan axis is for.

/// A global search with an objective and an admissible (never under-estimating) bound.
pub trait Bounded: GlobalSearch {
    fn value(&self, r: &Self::Space) -> u64;
    fn bound(&self, r: &Self::Space) -> u64;
}

/// Plan: prune any space whose bound cannot beat the incumbent; raise the incumbent on extract.
/// Pruning happens at the node's own unfold, after its earlier siblings have been explored.
pub struct BranchBound<'p, P: Bounded> { p: &'p P, pub incumbent: u64 }
impl<'p, P: Bounded> Plan<RoseF<(P::Space, bool)>> for BranchBound<'p, P> {
    type Seed = P::Space;
    fn unfold(&mut self, r: P::Space) -> ((P::Space, bool), Vec<P::Space>) {
        if self.p.bound(&r) <= self.incumbent && self.incumbent > 0 {
            return ((r, true), Vec::new());
        }
        if self.p.extract(&r) {
            self.incumbent = self.incumbent.max(self.p.value(&r));
        }
        let kids = self.p.split(&r).into_iter().filter(|c| self.p.filter(c)).collect();
        ((r, false), kids)
    }
}

/// Query: the maximum extracted value. Agrees with the incumbent; stated as a fold anyway so the
/// same tree could answer other queries.
pub struct Best<'p, P: Bounded> { p: &'p P }
impl<'p, P: Bounded> Algebra<RoseF<(P::Space, bool)>> for Best<'p, P> {
    type Out = u64;
    fn fold(&mut self, ((r, pruned), kids): ((P::Space, bool), Vec<u64>)) -> u64 {
        let here = if !pruned && self.p.extract(&r) { self.p.value(&r) } else { 0 };
        kids.into_iter().fold(here, u64::max)
    }
}

pub fn maximise<P: Bounded>(p: &P, x: &P::Input) -> u64 {
    let root = p.initial(x);
    hylo::<RoseF<(P::Space, bool)>, _, _>(&mut BranchBound { p, incumbent: 0 }, &mut Best { p }, root)
}

/// 0/1 knapsack. Space = (next item index, weight used, value so far).
pub struct Knapsack { pub items: Vec<(u64, u64)>, pub capacity: u64 } // (weight, value)
impl GlobalSearch for Knapsack {
    type Input = ();
    type Space = (usize, u64, u64);
    fn initial(&self, _: &()) -> Self::Space { (0, 0, 0) }
    fn split(&self, &(i, w, v): &Self::Space) -> Vec<Self::Space> {
        if i == self.items.len() { return Vec::new(); }
        let (wi, vi) = self.items[i];
        alloc::vec![(i + 1, w + wi, v + vi), (i + 1, w, v)]
    }
    fn filter(&self, &(_, w, _): &Self::Space) -> bool { w <= self.capacity }
    fn extract(&self, &(i, _, _): &Self::Space) -> bool { i == self.items.len() }
}
impl Bounded for Knapsack {
    fn value(&self, &(_, _, v): &Self::Space) -> u64 { v }
    /// Value so far plus the fractional relaxation of what remains: admissible.
    fn bound(&self, &(i, w, v): &Self::Space) -> u64 {
        let mut rest: Vec<(u64, u64)> = self.items[i..].to_vec();
        rest.sort_by(|a, b| (b.1 * a.0).cmp(&(a.1 * b.0))); // by value density, descending
        let (mut cap, mut b) = (self.capacity - w, v);
        for (wi, vi) in rest {
            if wi <= cap { cap -= wi; b += vi; } else { b += vi * cap / wi.max(1); break; }
        }
        b
    }
}
