//! The generic trace DP (Remark 3), written once for every construction grammar.
use crate::expr::{join, join_leaves, union, Expr, Val, Var};
use alloc::vec::Vec;

/// A construction of the input: a tree of operations.
#[derive(Clone, Debug)]
pub struct Node<Op> {
    pub op: Op,
    pub children: Vec<Node<Op>>,
}

/// One row of a DP table: the expression of all partial candidates with trace `tau`.
pub struct Row<Tau> {
    pub tau: Tau,
    pub expr: Expr,
}

pub type Table<Tau> = Vec<Row<Tau>>;

/// What `step` yields per child-row tuple: a new trace and the leaves it owns.
pub type Step<Tau> = Vec<(Tau, Vec<(Var, Val)>)>;

/// A problem expressed in the formalism.
///
/// Obligations (proved in Lean per instance, tested here):
/// 1. finitely many traces per node, bounded by `f(parameter)`;
/// 2. `accept` decides solutionhood from the trace alone;
/// 3. `step` is compositional: the trace of a candidate built by `op` from children with
///    traces `child_traces` is determined by those traces alone, and the candidate's
///    restriction to newly owned variables is exactly `leaves`.
pub trait Traced {
    type Op;
    type Tau: Clone + PartialEq;

    /// For `op` applied to one candidate from each child (given by trace), every resulting
    /// `(trace, owned leaves)`. Empty means the combination is not a partial solution.
    fn step(&self, op: &Self::Op, child_traces: &[Self::Tau]) -> Step<Self::Tau>;

    /// Whether a root candidate with this trace is a solution.
    fn accept(&self, tau: &Self::Tau) -> bool;
}

fn union_into<Tau: PartialEq>(table: &mut Table<Tau>, tau: Tau, e: Expr) {
    let mut i = 0;
    while i < table.len() {
        if table[i].tau == tau {
            let old = core::mem::replace(&mut table[i].expr, Expr::Empty);
            table[i].expr = union(old, e);
            return;
        }
        i += 1;
    }
    table.push(Row { tau, expr: e });
}

/// One DP step: the table of a node from `op` and its children's tables.
///
/// Invariant (Claim 1 of the paper): `⟦row(tau).expr⟧` is exactly the set of partial
/// candidates at this node whose trace is `tau`, restricted to owned variables.
/// Rows have distinct traces, so every `union` here is over disjoint sets, and every
/// `join` is over disjoint owned-variable domains: legality is by construction.
pub fn step_node<P: Traced>(p: &P, op: &P::Op, child_tables: Vec<Table<P::Tau>>) -> Table<P::Tau> {
    let mut table: Table<P::Tau> = Vec::new();
    let n = child_tables.len();
    let mut idx: Vec<usize> = Vec::new();
    let mut k = 0;
    while k < n {
        if child_tables[k].is_empty() { return table; }
        idx.push(0);
        k += 1;
    }

    loop {
        let mut traces: Vec<P::Tau> = Vec::new();
        let mut joined = Expr::Unit;
        let mut k = 0;
        while k < n {
            let row = &child_tables[k][idx[k]];
            traces.push(row.tau.clone());
            joined = join(joined, row.expr.clone());
            k += 1;
        }
        let outs = p.step(op, &traces);
        let mut o = 0;
        while o < outs.len() {
            let e = join_leaves(joined.clone(), &outs[o].1);
            union_into(&mut table, outs[o].0.clone(), e);
            o += 1;
        }

        // odometer over child rows
        let mut k = n;
        loop {
            if k == 0 { return table; }
            k -= 1;
            idx[k] += 1;
            if idx[k] < child_tables[k].len() { break; }
            idx[k] = 0;
        }
    }
}

/// Post-order fold of `step_node` over the construction. In `hylo` terms this is
/// `hylo(Project, TraceDp)` over `RoseF<Op>`; see `hylo::dp`.
pub fn run<P: Traced>(p: &P, node: &Node<P::Op>) -> Table<P::Tau> {
    let mut child_tables: Vec<Table<P::Tau>> = Vec::new();
    let mut c = 0;
    while c < node.children.len() {
        child_tables.push(run(p, &node.children[c]));
        c += 1;
    }
    step_node(p, &node.op, child_tables)
}

/// `⊎` of the rows of the root table whose trace is accepted: the expression of the
/// solution set.
pub fn solve<P: Traced>(p: &P, root: &Node<P::Op>) -> Expr {
    let table = run(p, root);
    let mut e = Expr::Empty;
    let mut i = 0;
    while i < table.len() {
        if p.accept(&table[i].tau) {
            e = union(e, table[i].expr.clone());
        }
        i += 1;
    }
    e
}
