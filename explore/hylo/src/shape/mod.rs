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
impl<D> IterAlgebra<D> for Last {
    type Out = D;
    fn fold(&mut self, l: Iter<D, D>) -> D { match l { Iter::Done(d) | Iter::Step(d) => d } }
}

// ---------------------------------------------------------------------------------------------
// Per-shape traits and hylos: the extractable core.
//
// Aeneas (upstream 0d21a9e) cannot translate the GAT `Shape::Layer<X>` nor a function that
// recurses through its own closure. So each shape also gets plain traits with the layer type
// spelled out and a hylo with direct recursion. The GAT traits above stay as the Rust-facing
// API; the blanket impls at the end make every per-shape plan or algebra usable there too.
// Extraction starts from the named algorithms (`charon --start-from`), which use these.
// ---------------------------------------------------------------------------------------------

pub trait ListPlan<T> { type Seed; fn unfold(&mut self, seed: Self::Seed) -> Option<(T, Self::Seed)>; }
pub trait ListAlgebra<T> { type Out; fn fold(&mut self, layer: Option<(T, Self::Out)>) -> Self::Out; }
pub fn hylo_list<T, P: ListPlan<T>, A: ListAlgebra<T>>(plan: &mut P, alg: &mut A, seed: P::Seed) -> A::Out {
    match plan.unfold(seed) {
        None => alg.fold(None),
        Some((h, next)) => { let r = hylo_list(plan, alg, next); alg.fold(Some((h, r))) }
    }
}

pub trait NodeTreePlan<T> { type Seed; fn unfold(&mut self, seed: Self::Seed) -> Option<(T, Self::Seed, Self::Seed)>; }
pub trait NodeTreeAlgebra<T> { type Out; fn fold(&mut self, layer: Option<(T, Self::Out, Self::Out)>) -> Self::Out; }
pub fn hylo_node_tree<T, P: NodeTreePlan<T>, A: NodeTreeAlgebra<T>>(plan: &mut P, alg: &mut A, seed: P::Seed) -> A::Out {
    match plan.unfold(seed) {
        None => alg.fold(None),
        Some((p, l, r)) => { let l = hylo_node_tree(plan, alg, l); let r = hylo_node_tree(plan, alg, r); alg.fold(Some((p, l, r))) }
    }
}

pub trait LeafTreePlan<T> { type Seed; fn unfold(&mut self, seed: Self::Seed) -> LeafTree<T, Self::Seed>; }
pub trait LeafTreeAlgebra<T> { type Out; fn fold(&mut self, layer: LeafTree<T, Self::Out>) -> Self::Out; }
pub fn hylo_leaf_tree<T, P: LeafTreePlan<T>, A: LeafTreeAlgebra<T>>(plan: &mut P, alg: &mut A, seed: P::Seed) -> A::Out {
    match plan.unfold(seed) {
        LeafTree::Leaf(t) => alg.fold(LeafTree::Leaf(t)),
        LeafTree::Node(l, r) => { let l = hylo_leaf_tree(plan, alg, l); let r = hylo_leaf_tree(plan, alg, r); alg.fold(LeafTree::Node(l, r)) }
    }
}

pub trait RosePlan<T> { type Seed; fn unfold(&mut self, seed: Self::Seed) -> (T, Vec<Self::Seed>); }
pub trait RoseAlgebra<T> { type Out; fn fold(&mut self, layer: (T, Vec<Self::Out>)) -> Self::Out; }
pub fn hylo_rose<T, P: RosePlan<T>, A: RoseAlgebra<T>>(plan: &mut P, alg: &mut A, seed: P::Seed) -> A::Out {
    let (t, mut kids) = plan.unfold(seed);
    // children in order, without iterator adaptors: pop from the back, then reverse by swaps
    let mut out: Vec<A::Out> = Vec::new();
    while let Some(k) = kids.pop() { out.push(hylo_rose(plan, alg, k)); }
    let n = out.len();
    let mut i = 0;
    while i < n / 2 { out.swap(i, n - 1 - i); i += 1; }
    alg.fold((t, out))
}

pub trait IterPlan<D> { type Seed; fn unfold(&mut self, seed: Self::Seed) -> Iter<D, Self::Seed>; }
pub trait IterAlgebra<D> { type Out; fn fold(&mut self, layer: Iter<D, Self::Out>) -> Self::Out; }
pub fn hylo_iter<D, P: IterPlan<D>, A: IterAlgebra<D>>(plan: &mut P, alg: &mut A, seed: P::Seed) -> A::Out {
    match plan.unfold(seed) {
        Iter::Done(d) => alg.fold(Iter::Done(d)),
        Iter::Step(x) => { let r = hylo_iter(plan, alg, x); alg.fold(Iter::Step(r)) }
    }
}

// Bridges into the GAT API.
impl<T, P: ListPlan<T>> crate::Plan<ListF<T>> for P { type Seed = P::Seed; fn unfold(&mut self, s: P::Seed) -> Option<(T, P::Seed)> { ListPlan::unfold(self, s) } }
impl<T, A: ListAlgebra<T>> crate::Algebra<ListF<T>> for A { type Out = A::Out; fn fold(&mut self, l: Option<(T, A::Out)>) -> A::Out { ListAlgebra::fold(self, l) } }
impl<T, P: NodeTreePlan<T>> crate::Plan<NodeTreeF<T>> for P { type Seed = P::Seed; fn unfold(&mut self, s: P::Seed) -> Option<(T, P::Seed, P::Seed)> { NodeTreePlan::unfold(self, s) } }
impl<T, A: NodeTreeAlgebra<T>> crate::Algebra<NodeTreeF<T>> for A { type Out = A::Out; fn fold(&mut self, l: Option<(T, A::Out, A::Out)>) -> A::Out { NodeTreeAlgebra::fold(self, l) } }
impl<T, P: LeafTreePlan<T>> crate::Plan<LeafTreeF<T>> for P { type Seed = P::Seed; fn unfold(&mut self, s: P::Seed) -> LeafTree<T, P::Seed> { LeafTreePlan::unfold(self, s) } }
impl<T, A: LeafTreeAlgebra<T>> crate::Algebra<LeafTreeF<T>> for A { type Out = A::Out; fn fold(&mut self, l: LeafTree<T, A::Out>) -> A::Out { LeafTreeAlgebra::fold(self, l) } }
impl<T, P: RosePlan<T>> crate::Plan<RoseF<T>> for P { type Seed = P::Seed; fn unfold(&mut self, s: P::Seed) -> (T, Vec<P::Seed>) { RosePlan::unfold(self, s) } }
impl<T, A: RoseAlgebra<T>> crate::Algebra<RoseF<T>> for A { type Out = A::Out; fn fold(&mut self, l: (T, Vec<A::Out>)) -> A::Out { RoseAlgebra::fold(self, l) } }
impl<D, P: IterPlan<D>> crate::Plan<IterF<D>> for P { type Seed = P::Seed; fn unfold(&mut self, s: P::Seed) -> Iter<D, P::Seed> { IterPlan::unfold(self, s) } }
impl<D, A: IterAlgebra<D>> crate::Algebra<IterF<D>> for A { type Out = A::Out; fn fold(&mut self, l: Iter<D, A::Out>) -> A::Out { IterAlgebra::fold(self, l) } }
