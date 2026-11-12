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
