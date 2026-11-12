//! Oracle tests for the H-colouring instance: the expression's set semantics must equal
//! brute force (Claim 1 at the root), and every semiring evaluation must agree with the
//! brute-force answer to its question.
use formalism::expr::{eval, semantics::semantics, Expr, Ones, Table, Val, Var};
use formalism::instances::hcol::{h, solve, Graph, HColoring, Invalid, NiceTd, Op};
use formalism::scheme::Node;
use formalism::semiring::{Boolean, Delta, Nat, Tropical};
use std::collections::BTreeSet;

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 { self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); self.0 >> 33 }
    fn below(&mut self, n: u64) -> u64 { if n == 0 { 0 } else { self.next() % n } }
    fn coin(&mut self) -> bool { self.next() & 1 == 1 }
}

/// A tree decomposition as a tree of bags with the connectivity property by construction:
/// each child bag is a subset of its parent's bag plus fresh variables.
struct BagTree { bag: Vec<Var>, children: Vec<BagTree> }

fn random_bag_tree(r: &mut Lcg, next_var: &mut Var, parent: &[Var], depth: u32, width: usize) -> BagTree {
    let mut bag: Vec<Var> = parent.iter().copied().filter(|_| r.coin()).collect();
    let fresh = r.below(width as u64 + 1) as usize;
    for _ in 0..fresh { bag.push(*next_var); *next_var += 1; }
    let mut children = Vec::new();
    if depth > 0 {
        for _ in 0..r.below(3) { children.push(random_bag_tree(r, next_var, &bag, depth - 1, width)); }
    }
    BagTree { bag, children }
}

/// Standard conversion to a nice tree decomposition. The first Introduce of each variable
/// (in construction order) owns it.
fn to_nice(t: &BagTree, owned: &mut BTreeSet<Var>) -> Node<Op> {
    fn introduce_all(mut n: Node<Op>, vars: &[Var], owned: &mut BTreeSet<Var>) -> Node<Op> {
        for &v in vars {
            let owner = owned.insert(v);
            n = Node { op: Op::Introduce { v, owner }, children: vec![n] };
        }
        n
    }
    fn forget_all(mut n: Node<Op>, vars: &[Var]) -> Node<Op> {
        for &v in vars { n = Node { op: Op::Forget { v }, children: vec![n] }; }
        n
    }
    if t.children.is_empty() {
        return introduce_all(Node { op: Op::Leaf, children: vec![] }, &t.bag, owned);
    }
    let mut branches: Vec<Node<Op>> = Vec::new();
    for c in &t.children {
        let sub = to_nice(c, owned);
        let drop: Vec<Var> = c.bag.iter().copied().filter(|v| !t.bag.contains(v)).collect();
        let add: Vec<Var> = t.bag.iter().copied().filter(|v| !c.bag.contains(v)).collect();
        branches.push(introduce_all(forget_all(sub, &drop), &add, owned));
    }
    let mut n = branches.pop().unwrap();
    while let Some(b) = branches.pop() {
        n = Node { op: Op::Join, children: vec![b, n] };
    }
    n
}

fn collect_bags(t: &BagTree, out: &mut Vec<Vec<Var>>) {
    out.push(t.bag.clone());
    for c in &t.children { collect_bags(c, out); }
}

/// Random instance: (G, nice TD of G). Edges are a random subset of pairs sharing a bag.
fn random_instance(seed: u64) -> (Graph, Node<Op>) {
    let mut r = Lcg(seed);
    let mut next_var = 0;
    let t = random_bag_tree(&mut r, &mut next_var, &[], 3, 2);
    let mut bags = Vec::new();
    collect_bags(&t, &mut bags);
    let mut g = Graph::new(next_var as usize);
    for b in &bags {
        for i in 0..b.len() { for j in i + 1..b.len() { if r.coin() { g.add_edge(b[i], b[j]); } } }
    }
    let mut owned = BTreeSet::new();
    let root = forget_all_root(to_nice(&t, &mut owned), &t.bag);
    (g, root)
}

fn forget_all_root(mut n: Node<Op>, vars: &[Var]) -> Node<Op> {
    for &v in vars { n = Node { op: Op::Forget { v }, children: vec![n] }; }
    n
}

fn brute_force(g: &Graph, hh: &Graph) -> BTreeSet<Vec<(Var, Val)>> {
    let n = g.n();
    let k = hh.n() as u64;
    let mut out = BTreeSet::new();
    let total = k.pow(n as u32);
    for code in 0..total {
        let mut f = Vec::new();
        let mut c = code;
        for v in 0..n { f.push((v as Var, (c % k) as Val)); c /= k; }
        let ok = (0..n).all(|u| g.adj[u].iter().all(|&v| hh.has_edge(f[u].1, f[v as usize].1)));
        if ok { out.insert(f); }
    }
    out
}

#[test]
fn expression_semantics_equal_brute_force() {
    for seed in 0..60 {
        let (g, root) = random_instance(seed);
        let td = NiceTd::new(&g, &root).unwrap_or_else(|e| panic!("seed {seed}: {e:?}"));
        for hh in [h::independent_set(), h::vertex_cover(), h::k_coloring(3)] {
            let p = HColoring { g: g.clone(), h: hh.clone() };
            let e = solve(&p, &td);
            let sem = semantics(&e).unwrap_or_else(|| panic!("seed {seed}: illegal expression"));
            assert_eq!(sem, brute_force(&g, &hh), "seed {seed}");
        }
    }
}

#[test]
fn every_semiring_answers_its_question() {
    for seed in 0..60 {
        let (g, root) = random_instance(seed);
        let td = NiceTd::new(&g, &root).unwrap();
        let hh = h::independent_set();
        let p = HColoring { g: g.clone(), h: hh.clone() };
        let e = solve(&p, &td);
        let sols = brute_force(&g, &hh);

        // decision
        assert_eq!(eval::<Boolean, _>(&e, &Ones).0, !sols.is_empty());
        // counting
        assert_eq!(eval::<Nat, _>(&e, &Ones).0, sols.len() as u64);

        // cost: weight(v, 1) = 0, weight(v, 0) = w_v  => minimises the weight left out,
        // i.e. maximum-weight independent set.
        let mut r = Lcg(seed ^ 0xbeef);
        let w = Table { rows: (0..g.n()).map(|_| vec![Tropical(1 + r.below(5)), Tropical(0)]).collect() };
        let cost = |f: &Vec<(Var, Val)>| f.iter().map(|&(v, d)| w.rows[v as usize][d as usize].0).sum::<u64>();
        let best = sols.iter().map(cost).min().unwrap();
        assert_eq!(eval::<Tropical, _>(&e, &w).0, best);

        // counting optima via the Δ-product (Theorem 6)
        let dw = Table { rows: w.rows.iter().map(|r| r.iter().map(|&t| Delta::new(t, Nat(1))).collect()).collect() };
        let d = eval::<Delta<Tropical, Nat>, _>(&e, &dw);
        assert_eq!(d.cost().0, best);
        assert_eq!(d.count().0, sols.iter().filter(|f| cost(f) == best).count() as u64);
    }
}

#[test]
fn size_is_polynomial() {
    // Each node adds O(|D|^{tw+1}) leaves; with tw <= 5 here the expression stays small.
    for seed in 0..20 {
        let (g, root) = random_instance(seed);
        let td = NiceTd::new(&g, &root).unwrap();
        let e = solve(&HColoring { g: g.clone(), h: h::k_coloring(3) }, &td);
        assert!(formalism::expr::size(&e) < 200_000, "seed {seed}");
    }
}

#[test]
fn invalid_decompositions_are_rejected() {
    let mut g = Graph::new(2);
    g.add_edge(0, 1);
    let leaf = || Node { op: Op::Leaf, children: vec![] };
    // 0 and 1 never share a bag
    let root = Node { op: Op::Forget { v: 1 }, children: vec![Node { op: Op::Introduce { v: 1, owner: true }, children: vec![
        Node { op: Op::Forget { v: 0 }, children: vec![Node { op: Op::Introduce { v: 0, owner: true }, children: vec![leaf()] }] }] }] };
    assert_eq!(NiceTd::new(&g, &root).err(), Some(Invalid::EdgeNotCovered(0, 1)));
    // nobody owns 1
    let root = Node { op: Op::Forget { v: 1 }, children: vec![Node { op: Op::Forget { v: 0 }, children: vec![
        Node { op: Op::Introduce { v: 1, owner: false }, children: vec![Node { op: Op::Introduce { v: 0, owner: true }, children: vec![leaf()] }] }] }] };
    assert_eq!(NiceTd::new(&g, &root).err(), Some(Invalid::Owners(1, 0)));
    // root bag not empty
    let root = Node { op: Op::Introduce { v: 0, owner: true }, children: vec![leaf()] };
    assert_eq!(NiceTd::new(&Graph::new(1), &root).err(), Some(Invalid::RootBagNotEmpty));
    let _ = Expr::Empty;
}
