//! Semiring-H-Coloring parameterised by tree-width (Theorem 8, Corollary 1, Algorithm 2).
//!
//! Solutions are maps `V_G -> V_H` sending edges of `G` to edges of `H`. This covers
//! k-Coloring (`H = K_k`), Independent Set (`H`: loop at 0, edge 0–1),
//! Vertex Cover (`H`: loop at 1, edge 0–1), and every binary CSP with one relation.
//! The semiring picks the question; `Table` weights pick the costs.
use crate::expr::{Val, Var};
use crate::scheme::{Node, Step, Traced};
use alloc::vec::Vec;

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
    pub fn has_edge(&self, u: u32, v: u32) -> bool {
        let row = &self.adj[u as usize];
        let mut i = 0;
        while i < row.len() {
            if row[i] == v { return true; }
            i += 1;
        }
        false
    }
    pub fn n(&self) -> usize { self.adj.len() }
}

pub struct HColoring {
    pub g: Graph,
    pub h: Graph,
}

/// Trace: the assignment restricted to the current bag, kept sorted by variable.
pub type Tau = Vec<(Var, Val)>;

fn insert_sorted(f: &Tau, v: Var, d: Val) -> Tau {
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

fn remove(f: &Tau, v: Var) -> Tau {
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
    fn consistent(&self, f: &Tau, v: Var, d: Val) -> bool {
        let mut i = 0;
        while i < f.len() {
            let (u, c) = f[i];
            if self.g.has_edge(u, v) && !self.h.has_edge(c, d) { return false; }
            i += 1;
        }
        if self.g.has_edge(v, v) && !self.h.has_edge(d, d) { return false; }
        true
    }
}

impl Traced for HColoring {
    type Op = Op;
    type Tau = Tau;

    fn step(&self, op: &Op, child: &[Tau]) -> Step<Tau> {
        let mut out = Vec::new();
        match op {
            Op::Leaf => out.push((Vec::new(), Vec::new())),
            Op::Introduce { v, owner } => {
                let f = &child[0];
                let mut d = 0;
                while d < self.h.n() as Val {
                    if self.consistent(f, *v, d) {
                        let mut leaves = Vec::new();
                        if *owner { leaves.push((*v, d)); }
                        out.push((insert_sorted(f, *v, d), leaves));
                    }
                    d += 1;
                }
            }
            Op::Forget { v } => out.push((remove(&child[0], *v), Vec::new())),
            Op::Join => {
                if child[0] == child[1] {
                    out.push((child[0].clone(), Vec::new()));
                }
            }
        }
        out
    }

    fn accept(&self, tau: &Tau) -> bool { tau.is_empty() }
}

/// Validation of a nice tree decomposition of `g`, i.e. Lemma 2 plus unique ownership.
/// A `Node<Op>` that passes is a construction of `g`; the DP is only run on those.
#[derive(Debug, PartialEq, Eq)]
pub enum Invalid {
    IntroduceAlreadyPresent(Var),
    ForgetNotInBag(Var),
    JoinBagsDiffer,
    Arity,
    RootBagNotEmpty,
    EdgeNotCovered(Var, Var),
    Owners(Var, usize),
}

struct Seen { bag: Vec<Var>, desc: Vec<Var> }

fn contains(xs: &[Var], v: Var) -> bool {
    let mut i = 0;
    while i < xs.len() { if xs[i] == v { return true; } i += 1; }
    false
}

fn check(g: &Graph, node: &Node<Op>, owners: &mut Vec<usize>, covered: &mut Vec<(Var, Var)>) -> Result<Seen, Invalid> {
    match &node.op {
        Op::Leaf => {
            if !node.children.is_empty() { return Err(Invalid::Arity); }
            Ok(Seen { bag: Vec::new(), desc: Vec::new() })
        }
        Op::Introduce { v, owner } => {
            if node.children.len() != 1 { return Err(Invalid::Arity); }
            let c = check(g, &node.children[0], owners, covered)?;
            if contains(&c.desc, *v) { return Err(Invalid::IntroduceAlreadyPresent(*v)); }
            if *owner { owners[*v as usize] += 1; }
            let mut bag = c.bag.clone();
            let mut i = 0;
            while i < bag.len() {
                if g.has_edge(bag[i], *v) { covered.push((bag[i], *v)); covered.push((*v, bag[i])); }
                i += 1;
            }
            bag.push(*v);
            let mut desc = c.desc;
            desc.push(*v);
            Ok(Seen { bag, desc })
        }
        Op::Forget { v } => {
            if node.children.len() != 1 { return Err(Invalid::Arity); }
            let c = check(g, &node.children[0], owners, covered)?;
            if !contains(&c.bag, *v) { return Err(Invalid::ForgetNotInBag(*v)); }
            let mut bag = Vec::new();
            let mut i = 0;
            while i < c.bag.len() { if c.bag[i] != *v { bag.push(c.bag[i]); } i += 1; }
            Ok(Seen { bag, desc: c.desc })
        }
        Op::Join => {
            if node.children.len() != 2 { return Err(Invalid::Arity); }
            let a = check(g, &node.children[0], owners, covered)?;
            let b = check(g, &node.children[1], owners, covered)?;
            let mut i = 0;
            while i < a.bag.len() { if !contains(&b.bag, a.bag[i]) { return Err(Invalid::JoinBagsDiffer); } i += 1; }
            if a.bag.len() != b.bag.len() { return Err(Invalid::JoinBagsDiffer); }
            // descbag(N1) ∩ descbag(N2) ⊆ bag(N)
            let mut i = 0;
            while i < a.desc.len() {
                if contains(&b.desc, a.desc[i]) && !contains(&a.bag, a.desc[i]) {
                    return Err(Invalid::IntroduceAlreadyPresent(a.desc[i]));
                }
                i += 1;
            }
            let mut desc = a.desc;
            let mut i = 0;
            while i < b.desc.len() { if !contains(&desc, b.desc[i]) { desc.push(b.desc[i]); } i += 1; }
            Ok(Seen { bag: a.bag, desc })
        }
    }
}

/// A validated construction of `g`. Only this can be solved.
pub struct NiceTd<'a> {
    pub root: &'a Node<Op>,
}

impl<'a> NiceTd<'a> {
    pub fn new(g: &Graph, root: &'a Node<Op>) -> Result<Self, Invalid> {
        let mut owners = Vec::new();
        let mut i = 0;
        while i < g.n() { owners.push(0usize); i += 1; }
        let mut covered = Vec::new();
        let seen = check(g, root, &mut owners, &mut covered)?;
        if !seen.bag.is_empty() { return Err(Invalid::RootBagNotEmpty); }
        let mut v = 0;
        while v < g.n() {
            if contains(&seen.desc, v as Var) && owners[v] != 1 { return Err(Invalid::Owners(v as Var, owners[v])); }
            let row = &g.adj[v];
            let mut j = 0;
            while j < row.len() {
                let u = row[j];
                if u != v as Var {
                    let mut found = false;
                    let mut k = 0;
                    while k < covered.len() { if covered[k] == (v as Var, u) { found = true; break; } k += 1; }
                    if !found { return Err(Invalid::EdgeNotCovered(v as Var, u)); }
                }
                j += 1;
            }
            v += 1;
        }
        Ok(NiceTd { root })
    }
}

/// Solve on a validated decomposition: the expression of all H-colourings of `g`.
pub fn solve(p: &HColoring, td: &NiceTd<'_>) -> crate::expr::Expr {
    crate::scheme::solve(p, td.root)
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
