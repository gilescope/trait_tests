//! Reduce and scan over a monoid. Knuth 4.6 / Blelloch 1989 / Elliott 2017.
//! The plan (how the sequence is split) is free by the third homomorphism theorem.
use crate::algebra::Monoid;
use crate::shape::{LeafTree, LeafTreeF, ListF};
use crate::sort::{Halve, Uncons};
use crate::{hylo, Algebra};
use alloc::vec::Vec;

/// Reduce as a fold over the list shape: sequential.
pub struct ReduceL<M>(core::marker::PhantomData<M>);
impl<M: Monoid> Algebra<ListF<M>> for ReduceL<M> {
    type Out = M;
    fn fold(&mut self, l: Option<(M, M)>) -> M { match l { None => M::unit(), Some((h, t)) => h.op(t) } }
}

/// Reduce as a fold over the leaf tree: the parallel shape.
pub struct ReduceT<M>(core::marker::PhantomData<M>);
impl<M: Monoid> Algebra<LeafTreeF<M>> for ReduceT<M> {
    type Out = M;
    fn fold(&mut self, l: LeafTree<M, M>) -> M {
        match l { LeafTree::Leaf(x) => x.unwrap_or_else(M::unit), LeafTree::Node(a, b) => a.op(b) }
    }
}

/// Sklansky's scan: fold returns (total, inclusive prefixes); the right half is shifted by the left total.
pub struct Scan<M>(core::marker::PhantomData<M>);
impl<M: Monoid> Algebra<LeafTreeF<M>> for Scan<M> {
    type Out = (M, Vec<M>);
    fn fold(&mut self, l: LeafTree<M, (M, Vec<M>)>) -> (M, Vec<M>) {
        match l {
            LeafTree::Leaf(None) => (M::unit(), Vec::new()),
            LeafTree::Leaf(Some(x)) => (x, alloc::vec![x]),
            LeafTree::Node((tl, mut pl), (tr, pr)) => {
                pl.extend(pr.into_iter().map(|x| tl.op(x)));
                (tl.op(tr), pl)
            }
        }
    }
}

pub fn reduce_seq<M: Monoid>(v: Vec<M>) -> M { hylo::<ListF<M>, _, _>(&mut Uncons, &mut ReduceL(core::marker::PhantomData), v) }
pub fn reduce_par<M: Monoid>(v: Vec<M>) -> M { hylo::<LeafTreeF<M>, _, _>(&mut Halve, &mut ReduceT(core::marker::PhantomData), v) }
pub fn scan<M: Monoid>(v: Vec<M>) -> Vec<M> { hylo::<LeafTreeF<M>, _, _>(&mut Halve, &mut Scan(core::marker::PhantomData), v).1 }
