//! Validation of a nice tree decomposition (Lemma 2 plus unique ownership), and `solve` on a
//! validated one. Not extracted: it uses `?` and early returns.
use super::hcol::{Graph, HColoring, Op};
use crate::expr::Var;
use crate::scheme::Node;
use alloc::vec::Vec;

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
    // No early returns inside loops (Aeneas limitation): loops record a failure, the function
    // returns after them.
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
            let mut bags_differ = a.bag.len() != b.bag.len();
            let mut i = 0;
            while i < a.bag.len() { if !contains(&b.bag, a.bag[i]) { bags_differ = true; } i += 1; }
            if bags_differ { return Err(Invalid::JoinBagsDiffer); }
            // descbag(N1) ∩ descbag(N2) ⊆ bag(N)
            let mut leaked: Option<Var> = None;
            let mut i = 0;
            while i < a.desc.len() {
                if contains(&b.desc, a.desc[i]) && !contains(&a.bag, a.desc[i]) && leaked.is_none() {
                    leaked = Some(a.desc[i]);
                }
                i += 1;
            }
            if let Some(v) = leaked { return Err(Invalid::IntroduceAlreadyPresent(v)); }
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
        // scan for the first violation; return after the loops
        let mut problem: Option<Invalid> = None;
        let mut v = 0;
        while v < g.n() {
            if contains(&seen.desc, v as Var) && owners[v] != 1 && problem.is_none() {
                problem = Some(Invalid::Owners(v as Var, owners[v]));
            }
            let row = &g.adj[v];
            let mut j = 0;
            while j < row.len() {
                let u = row[j];
                if u != v as Var {
                    let mut found = false;
                    let mut k = 0;
                    while k < covered.len() { if covered[k] == (v as Var, u) { found = true; } k += 1; }
                    if !found && problem.is_none() { problem = Some(Invalid::EdgeNotCovered(v as Var, u)); }
                }
                j += 1;
            }
            v += 1;
        }
        match problem { Some(e) => Err(e), None => Ok(NiceTd { root }) }
    }
}

/// Solve on a validated decomposition: the expression of all H-colourings of `g`.
pub fn solve(p: &HColoring, td: &NiceTd<'_>) -> crate::expr::Expr {
    crate::scheme::solve(p, td.root)
}
