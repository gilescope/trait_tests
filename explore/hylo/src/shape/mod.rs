//! Shapes: one owned layer each.
use crate::Shape;
use alloc::vec::Vec;
use core::marker::PhantomData;

/// Nil | Cons(head, rest). Knuth 5.2.1 / 5.2.3 sorts, sequential search.
pub struct ListF<T>(PhantomData<T>);
impl<T> Shape for ListF<T> {
    type Layer<X> = Option<(T, X)>;
    fn map<A, B>(l: Option<(T, A)>, mut f: impl FnMut(A) -> B) -> Option<(T, B)> { l.map(|(h, x)| (h, f(x))) }
}

/// Leaf | Node(pivot, left, right): data at the nodes. Quicksort, treesort, BSTs.
pub struct NodeTreeF<T>(PhantomData<T>);
impl<T> Shape for NodeTreeF<T> {
    type Layer<X> = Option<(T, X, X)>;
    fn map<A, B>(l: Option<(T, A, A)>, mut f: impl FnMut(A) -> B) -> Option<(T, B, B)> {
        l.map(|(p, a, b)| { let a = f(a); (p, a, f(b)) })
    }
}

/// Leaf(Option<T>) | Node(left, right): data at the leaves. Mergesort, FFT, scans.
pub enum LeafTree<T, X> { Leaf(Option<T>), Node(X, X) }
pub struct LeafTreeF<T>(PhantomData<T>);
impl<T> Shape for LeafTreeF<T> {
    type Layer<X> = LeafTree<T, X>;
    fn map<A, B>(l: LeafTree<T, A>, mut f: impl FnMut(A) -> B) -> LeafTree<T, B> {
        match l { LeafTree::Leaf(t) => LeafTree::Leaf(t), LeafTree::Node(a, b) => { let a = f(a); LeafTree::Node(a, f(b)) } }
    }
}

/// (label, children): n-ary. DFS forests, search trees, backtracking.
pub struct RoseF<T>(PhantomData<T>);
impl<T> Shape for RoseF<T> {
    type Layer<X> = (T, Vec<X>);
    fn map<A, B>((t, xs): (T, Vec<A>), f: impl FnMut(A) -> B) -> (T, Vec<B>) { (t, xs.into_iter().map(f).collect()) }
}

/// Done(result) | Step(next): the shape of iteration to a fixpoint. Relaxation, closure, local search.
/// A hylo over it is a loop; the plan's recursiveness obligation is the termination proof.
pub enum Iter<D, X> { Done(D), Step(X) }
pub struct IterF<D>(PhantomData<D>);
impl<D> Shape for IterF<D> {
    type Layer<X> = Iter<D, X>;
    fn map<A, B>(l: Iter<D, A>, mut f: impl FnMut(A) -> B) -> Iter<D, B> {
        match l { Iter::Done(d) => Iter::Done(d), Iter::Step(x) => Iter::Step(f(x)) }
    }
}

/// The algebra that just returns the fixpoint. Pairs with `IterF`.
pub struct Last;
impl<D> crate::Algebra<IterF<D>> for Last {
    type Out = D;
    fn fold(&mut self, l: Iter<D, D>) -> D { match l { Iter::Done(d) | Iter::Step(d) => d } }
}
