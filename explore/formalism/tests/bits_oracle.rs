//! Oracle test for the `Bits` instance: the expression's set semantics must be exactly the
//! assignments of the tree's leaves with `k` ones (Claim 1 at the root).
use formalism::expr::{semantics::semantics, Var};
use formalism::instances::bits::{Bits, Op};
use formalism::scheme::{solve, Node};
use std::collections::BTreeSet;

fn leaf(v: Var) -> Node<Op> { Node { op: Op::Leaf(v), children: Vec::new() } }
fn node(children: Vec<Node<Op>>) -> Node<Op> { Node { op: Op::Node, children } }

fn leaves(n: &Node<Op>, out: &mut Vec<Var>) {
    if let Op::Leaf(v) = n.op { out.push(v); }
    for c in &n.children { leaves(c, out); }
}

fn brute(vars: &[Var], k: u64) -> BTreeSet<Vec<(Var, u32)>> {
    let mut out = BTreeSet::new();
    for mask in 0u64..(1u64 << vars.len()) {
        if mask.count_ones() as u64 != k { continue; }
        let mut a: Vec<(Var, u32)> = vars.iter().enumerate().map(|(i, v)| (*v, ((mask >> i) & 1) as u32)).collect();
        a.sort();
        out.insert(a);
    }
    out
}

fn check(root: &Node<Op>) {
    let mut vars = Vec::new();
    leaves(root, &mut vars);
    for k in 0..=(vars.len() as u64 + 1) {
        let e = solve(&Bits { k }, root);
        let got = semantics(&e).expect("legal expression");
        assert_eq!(got, brute(&vars, k), "k = {k}");
    }
}

#[test]
fn bits_matches_brute_force() {
    check(&leaf(0));
    check(&node(vec![]));
    check(&node(vec![leaf(0), leaf(1), leaf(2)]));
    check(&node(vec![node(vec![leaf(0), leaf(1)]), leaf(2), node(vec![node(vec![leaf(3)]), leaf(4)])]));
    check(&node(vec![node(vec![]), leaf(5), node(vec![leaf(6), node(vec![leaf(7), leaf(8)])])]));
}
