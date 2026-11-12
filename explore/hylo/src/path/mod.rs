//! Knuth 7.3: shortest distances as `Relax<S, Q>` over the iteration shape, and `closure` over a matrix.
//! Bellman-Ford = Relax<Tropical, Fifo>. Dijkstra = Relax<Tropical, ShortestFirst>.
//! Reachability = Relax<Boolean, _>. Floyd–Warshall = closure::<Tropical>. Warshall = closure::<Boolean>.
use crate::algebra::{KClosed, Semiring, Star, Superior};
use crate::shape::{Iter, IterF, Last};
use crate::{hylo, Plan};
use alloc::collections::{BinaryHeap, VecDeque};
use alloc::vec::Vec;
use core::cmp::Reverse;

pub type Node = usize;
pub struct Graph<S> { pub adj: Vec<Vec<(Node, S)>> }

/// Queue discipline: the part of the plan that the homomorphism theorem says is free.
pub trait Queue<S>: Default {
    fn push(&mut self, n: Node, key: S);
    fn pop(&mut self) -> Option<Node>;
}
#[derive(Default)] pub struct Fifo(VecDeque<Node>);
impl<S> Queue<S> for Fifo {
    fn push(&mut self, n: Node, _: S) { self.0.push_back(n) }
    fn pop(&mut self) -> Option<Node> { self.0.pop_front() }
}
/// Requires `Superior` so that each node is settled when first popped.
pub struct ShortestFirst<S: Ord>(BinaryHeap<Reverse<(S, Node)>>);
impl<S: Ord> Default for ShortestFirst<S> { fn default() -> Self { ShortestFirst(BinaryHeap::new()) } }
impl<S: Superior + Ord> Queue<S> for ShortestFirst<S> {
    fn push(&mut self, n: Node, key: S) { self.0.push(Reverse((key, n))) }
    fn pop(&mut self) -> Option<Node> { self.0.pop().map(|Reverse((_, n))| n) }
}

/// Mohri's generic single-source shortest-distance algorithm as a plan over `IterF`.
/// State: d (distances), r (unsettled contribution, needed when ⊕ is not idempotent), queue, in-queue flags.
pub struct Relax<'g, S, Q> { g: &'g Graph<S>, q: Q, inq: Vec<bool> }
pub struct State<S> { pub d: Vec<S>, pub r: Vec<S> }

impl<'g, S: Semiring + KClosed<0>, Q: Queue<S>> Plan<IterF<Vec<S>>> for Relax<'g, S, Q> {
    type Seed = State<S>;
    fn unfold(&mut self, mut st: State<S>) -> Iter<Vec<S>, State<S>> {
        let Some(q) = self.q.pop() else { return Iter::Done(st.d) };
        self.inq[q] = false;
        let rq = core::mem::replace(&mut st.r[q], S::zero());
        for &(n, w) in &self.g.adj[q] {
            let via = rq.mul(w);
            let d2 = st.d[n].add(via);
            if d2 != st.d[n] {
                st.d[n] = d2;
                st.r[n] = st.r[n].add(via);
                if !self.inq[n] { self.inq[n] = true; self.q.push(n, d2); }
            }
        }
        Iter::Step(st)
    }
}

/// The named pair. `Q` is free by Mohri's Theorem 1; `S: KClosed<0>` is the hypothesis.
pub fn relax<S: Semiring + KClosed<0>, Q: Queue<S>>(g: &Graph<S>, s: Node) -> Vec<S> {
    let n = g.adj.len();
    let mut d = alloc::vec![S::zero(); n];
    let mut r = alloc::vec![S::zero(); n];
    d[s] = S::one();
    r[s] = S::one();
    let mut plan = Relax { g, q: Q::default(), inq: alloc::vec![false; n] };
    plan.inq[s] = true;
    plan.q.push(s, S::one());
    hylo::<IterF<Vec<S>>, _, _>(&mut plan, &mut Last, State { d, r })
}

/// Lehmann's closure over a dense matrix, as a plan over `IterF` indexed by k.
/// Boolean → Warshall, Tropical → Floyd–Warshall, regex → Kleene, reals → Gauss–Jordan.
pub struct Lehmann { k: usize }
impl<S: Star> Plan<IterF<Vec<Vec<S>>>> for Lehmann {
    type Seed = Vec<Vec<S>>;
    fn unfold(&mut self, mut m: Vec<Vec<S>>) -> Iter<Vec<Vec<S>>, Vec<Vec<S>>> {
        let n = m.len();
        if self.k == n {
            for (i, row) in m.iter_mut().enumerate() { row[i] = row[i].add(S::one()); } // the final "1 +"
            return Iter::Done(m);
        }
        let k = self.k;
        let kk = m[k][k].star();
        for i in 0..n { for j in 0..n {
            m[i][j] = m[i][j].add(m[i][k].mul(kk).mul(m[k][j]));
        } }
        self.k += 1;
        Iter::Step(m)
    }
}
pub fn closure<S: Star>(m: Vec<Vec<S>>) -> Vec<Vec<S>> {
    hylo::<IterF<Vec<Vec<S>>>, _, _>(&mut Lehmann { k: 0 }, &mut Last, m)
}

impl<S: Semiring> Graph<S> {
    pub fn matrix(&self) -> Vec<Vec<S>> {
        let n = self.adj.len();
        let mut m = alloc::vec![alloc::vec![S::zero(); n]; n];
        for (u, es) in self.adj.iter().enumerate() { for &(v, w) in es { m[u][v] = m[u][v].add(w); } }
        m
    }
}
