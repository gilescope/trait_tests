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

/// How a solution is weighed in a carrier. The default, `one`, gives exists and count.
/// A cost gives optimisation; `Delta::new(cost, Nat(1))` gives the number of optima (Theorem 6).
pub trait Weigh<S: Semiring>: GlobalSearch {
    fn weigh(&self, _r: &Self::Space) -> S { S::one() }
}

/// The query: a semiring over the search tree. Extracted leaves contribute their weight.
pub struct Aggregate<'p, P: GlobalSearch, S> { p: &'p P, _s: core::marker::PhantomData<S> }
impl<'p, P: Weigh<S>, S: Semiring> Algebra<RoseF<P::Space>> for Aggregate<'p, P, S> {
    type Out = S;
    fn fold(&mut self, (r, kids): (P::Space, Vec<S>)) -> S {
        let here = if self.p.extract(&r) { self.p.weigh(&r) } else { S::zero() };
        kids.into_iter().fold(here, S::add)
    }
}

pub fn search<P: Weigh<S>, S: Semiring>(p: &P, x: &P::Input) -> S {
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
impl Weigh<crate::algebra::Boolean> for Queens {}
impl Weigh<crate::algebra::Nat> for Queens {}
/// Cost of a placement: the sum of its columns. Arbitrary, but it has ties, which is the point.
impl Weigh<crate::algebra::Tropical> for Queens {
    fn weigh(&self, (_, cols): &Self::Space) -> crate::algebra::Tropical { crate::algebra::Tropical(cols.iter().map(|&c| c as u64).sum()) }
}
impl Weigh<crate::algebra::Delta<crate::algebra::Tropical, crate::algebra::Nat>> for Queens {
    fn weigh(&self, r: &Self::Space) -> crate::algebra::Delta<crate::algebra::Tropical, crate::algebra::Nat> {
        crate::algebra::Delta::new(<Self as Weigh<crate::algebra::Tropical>>::weigh(self, r), crate::algebra::Nat(1))
    }
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
///
/// `cut_ties` is the product obligation made concrete: a query that only wants the optimum may
/// cut a space whose bound merely equals the incumbent; a query that counts optima may not,
/// because that space can hold more of them (Steffen & Giegerich, Theorem 1(3)).
pub struct BranchBound<'p, P: Bounded> { p: &'p P, pub incumbent: u64, pub cut_ties: bool }
impl<'p, P: Bounded> Plan<RoseF<(P::Space, bool)>> for BranchBound<'p, P> {
    type Seed = P::Space;
    fn unfold(&mut self, r: P::Space) -> ((P::Space, bool), Vec<P::Space>) {
        let b = self.p.bound(&r);
        if b < self.incumbent || (self.cut_ties && b == self.incumbent && self.incumbent > 0) {
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
    hylo::<RoseF<(P::Space, bool)>, _, _>(&mut BranchBound { p, incumbent: 0, cut_ties: true }, &mut Best { p }, root)
}

/// Query: the Δ-product `MaxPlus Δ Nat` over the pruned tree: (optimum, number of optima).
pub struct BestCount<'p, P: Bounded> { p: &'p P }
impl<'p, P: Bounded> Algebra<RoseF<(P::Space, bool)>> for BestCount<'p, P> {
    type Out = crate::algebra::Delta<crate::algebra::MaxPlus, crate::algebra::Nat>;
    fn fold(&mut self, ((r, pruned), kids): ((P::Space, bool), Vec<Self::Out>)) -> Self::Out {
        use crate::algebra::{Delta, MaxPlus, Nat, Semiring};
        let here = if !pruned && self.p.extract(&r) { Delta::new(MaxPlus(Some(self.p.value(&r))), Nat(1)) } else { Delta::zero() };
        kids.into_iter().fold(here, Delta::add)
    }
}

/// Same plan with ties kept: the count is only right because `cut_ties` is false.
pub fn maximise_count<P: Bounded>(p: &P, x: &P::Input) -> (u64, u64) {
    let root = p.initial(x);
    let d = hylo::<RoseF<(P::Space, bool)>, _, _>(&mut BranchBound { p, incumbent: 0, cut_ties: false }, &mut BestCount { p }, root);
    (d.cost().0.unwrap_or(0), d.count().0)
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

/// Knuth 6.2.1: binary search is global search over index ranges (Smith's Or-reduction).
/// The filter is the sortedness argument: the target can only live where lo ≤ target ≤ hi.
/// Over `Nat` the same search counts occurrences; over `Boolean` it is `contains`.
pub struct BinarySearch<'a, T> { pub sorted: &'a [T], pub target: T }
impl<'a, T: Ord + Clone> GlobalSearch for BinarySearch<'a, T> {
    type Input = ();
    type Space = (usize, usize); // half-open range
    fn initial(&self, _: &()) -> Self::Space { (0, self.sorted.len()) }
    fn split(&self, &(lo, hi): &Self::Space) -> Vec<Self::Space> {
        if hi - lo <= 1 { return Vec::new(); }
        let mid = lo + (hi - lo) / 2;
        alloc::vec![(lo, mid), (mid, hi)]
    }
    fn filter(&self, &(lo, hi): &Self::Space) -> bool {
        lo < hi && self.sorted[lo] <= self.target && self.target <= self.sorted[hi - 1]
    }
    fn extract(&self, &(lo, hi): &Self::Space) -> bool { hi - lo == 1 && self.sorted[lo] == self.target }
}
impl<'a, T: Ord + Clone> Weigh<crate::algebra::Boolean> for BinarySearch<'a, T> {}
impl<'a, T: Ord + Clone> Weigh<crate::algebra::Nat> for BinarySearch<'a, T> {}
