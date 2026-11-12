//! algorithm = hylo(plan, algebra) : Seed → Out, over a Shape.
//!
//! * `Shape`   : F, one layer of the virtual structure. Layers are owned: no lifetime GATs.
//! * `Plan`    : c, the unfold step. A type, so it has a name (`Pivot`, `Fifo`) and holds its state.
//! * `Algebra` : a, the fold step. A type; its impls are the queries (`Concat`, `Last`).
//! * `hylo`    : the one scheme. Termination is the plan's obligation: `unfold` must be recursive.
//!
//! Named algorithms are pairs: quicksort = `(Pivot, Concat)`, Bellman-Ford = `Relax<Tropical, Fifo>`.
#![no_std]
extern crate alloc;

pub mod algebra;
pub mod path;
pub mod shape;
pub mod sort;

/// One layer of the virtual structure, parameterised by what sits in the recursive positions.
pub trait Shape {
    type Layer<X>;
    fn map<A, B>(layer: Self::Layer<A>, f: impl FnMut(A) -> B) -> Self::Layer<B>;
}

/// The unfold step. Obligation: recursive (every unfolding bottoms out). Knuth's finiteness.
pub trait Plan<S: Shape> {
    type Seed;
    fn unfold(&mut self, seed: Self::Seed) -> S::Layer<Self::Seed>;
}

/// The fold step. Its laws decide which theorems fire (fusion, homomorphism).
pub trait Algebra<S: Shape> {
    type Out;
    fn fold(&mut self, layer: S::Layer<Self::Out>) -> Self::Out;
}

/// hylo(a, c) = a ∘ F(hylo(a, c)) ∘ c
pub fn hylo<S: Shape, P: Plan<S>, A: Algebra<S>>(plan: &mut P, alg: &mut A, seed: P::Seed) -> A::Out {
    let layer = plan.unfold(seed);
    let folded = S::map(layer, |x| hylo::<S, P, A>(plan, alg, x));
    alg.fold(folded)
}
