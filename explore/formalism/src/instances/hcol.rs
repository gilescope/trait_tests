//! Semiring-H-Coloring parameterised by tree-width (Theorem 8, Corollary 1, Algorithm 2).
//!
//! Solutions are maps `V_G -> V_H` sending edges of `G` to edges of `H`. This covers
//! k-Coloring (`H = K_k`), Independent Set (`H`: loop at 0, edge 0–1),
//! Vertex Cover (`H`: loop at 1, edge 0–1), and every binary CSP with one relation.
//! The semiring picks the question; `Table` weights pick the costs.
//!
//! This module is the extractable core (Aeneas's subset: index loops, no early `return` in a
//! loop, no iterator adaptors). Validating a decomposition is in `hcol_td`.
use crate::expr::{Val, Var};
use crate::scheme::{Step, Traced};
use alloc::vec::Vec;

pub use super::hcol_td::{solve, Invalid, NiceTd};

/// Nodes of a nice tree decomposition, read as a construction of `G` (Section 6.1).
/// `owner` marks the one Introduce node λ(v) that owns `v`'s leaf in the expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op {
    Leaf,
    Introduce { v: Var, owner: bool },
    Forget { v: Var },
    Join,
}

/// Simple graphs on `0..n` as adjacency lists, loops allowed (needed for `H`).
#[derive(Clone, Debug, Default)]
pub struct Graph {
    pub adj: Vec<Vec<u32>>,
}

impl Graph {
    pub fn new(n: usize) -> Self {
        let mut adj = Vec::new();
        let mut i = 0;
        while i < n { adj.push(Vec::new()); i += 1; }
        Graph { adj }
    }
    pub fn add_edge(&mut self, u: u32, v: u32) {
        if !self.has_edge(u, v) {
            self.adj[u as usize].push(v);
            if u != v { self.adj[v as usize].push(u); }
        }
    }
    // A vertex outside the graph has no edges (so this is total, which the refinement needs).
    // No early `return` inside a loop: Aeneas does not translate those.
    pub fn has_edge(&self, u: u32, v: u32) -> bool {
        let mut found = false;
        if (u as usize) < self.adj.len() {
            let row = &self.adj[u as usize];
            let mut i = 0;
            while i < row.len() {
                if row[i] == v { found = true; }
                i += 1;
            }
        }
        found
    }
    pub fn n(&self) -> usize { self.adj.len() }
}

pub struct HColoring {
    pub g: Graph,
    pub h: Graph,
}

/// Trace: the assignment restricted to the current bag, kept sorted by variable. A struct with
/// its own `Clone` and `PartialEq` (element loops), so that the extraction needs no library
/// model of `Vec`'s.
pub struct Tau(pub Vec<(Var, Val)>);

impl Clone for Tau {
    fn clone(&self) -> Tau {
        let mut out = Vec::new();
        let mut i = 0;
        while i < self.0.len() { out.push(self.0[i]); i += 1; }
        Tau(out)
    }
}

fn same(a: &[(Var, Val)], b: &[(Var, Val)]) -> bool {
    let mut eq = a.len() == b.len();
    let mut i = 0;
    while i < a.len() && i < b.len() {
        if a[i].0 != b[i].0 || a[i].1 != b[i].1 { eq = false; }
        i += 1;
    }
    eq
}

impl PartialEq for Tau {
    fn eq(&self, other: &Tau) -> bool { same(&self.0, &other.0) }
}
impl Eq for Tau {}

impl core::fmt::Debug for Tau {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result { self.0.fmt(f) }
}

fn insert_sorted(f: &[(Var, Val)], v: Var, d: Val) -> Vec<(Var, Val)> {
    let mut out = Vec::new();
    let mut placed = false;
    let mut i = 0;
    while i < f.len() {
        if !placed && f[i].0 > v {
            out.push((v, d));
            placed = true;
        }
        out.push(f[i]);
        i += 1;
    }
    if !placed { out.push((v, d)); }
    out
}

fn remove(f: &[(Var, Val)], v: Var) -> Vec<(Var, Val)> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < f.len() {
        if f[i].0 != v { out.push(f[i]); }
        i += 1;
    }
    out
}

impl HColoring {
    /// `f ∪ {v ↦ d}` respects every `G`-edge between `v` and the bag (Lemma 2 says
    /// those are the only edges at `v` inside `descbag`).
    fn consistent(&self, f: &[(Var, Val)], v: Var, d: Val) -> bool {
        let mut ok = true;
        let mut i = 0;
        while i < f.len() {
            let (u, c) = f[i];
            if self.g.has_edge(u, v) && !self.h.has_edge(c, d) { ok = false; }
            i += 1;
        }
        if self.g.has_edge(v, v) && !self.h.has_edge(d, d) { ok = false; }
        ok
    }
}

impl Traced for HColoring {
    type Op = Op;
    type Tau = Tau;

    fn step(&self, op: &Op, child: &[Tau]) -> Step<Tau> {
        let mut out = Vec::new();
        match op {
            Op::Leaf => out.push((Tau(Vec::new()), Vec::new())),
            Op::Introduce { v, owner } => {
                let f = &child[0].0;
                let mut d = 0;
                while d < self.h.n() as Val {
                    if self.consistent(f, *v, d) {
                        let mut leaves = Vec::new();
                        if *owner { leaves.push((*v, d)); }
                        out.push((Tau(insert_sorted(f, *v, d)), leaves));
                    }
                    d += 1;
                }
            }
            Op::Forget { v } => out.push((Tau(remove(&child[0].0, *v)), Vec::new())),
            Op::Join => {
                if same(&child[0].0, &child[1].0) {
                    out.push((child[0].clone(), Vec::new()));
                }
            }
        }
        out
    }

    fn accept(&self, tau: &Tau) -> bool { tau.0.is_empty() }
}

/// Well-known `H` graphs.
pub mod h {
    use super::Graph;
    /// Independent set: colour 1 = in the set. 1–1 forbidden.
    pub fn independent_set() -> Graph { let mut h = Graph::new(2); h.add_edge(0, 0); h.add_edge(0, 1); h }
    /// Vertex cover: colour 1 = in the cover. 0–0 forbidden.
    pub fn vertex_cover() -> Graph { let mut h = Graph::new(2); h.add_edge(1, 1); h.add_edge(0, 1); h }
    /// Proper k-colouring: `K_k`.
    pub fn k_coloring(k: u32) -> Graph {
        let mut h = Graph::new(k as usize);
        let mut a = 0;
        while a < k { let mut b = a + 1; while b < k { h.add_edge(a, b); b += 1; } a += 1; }
        h
    }
}
