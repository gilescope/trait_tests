//! Every named algorithm is a pair; the oracle is brute force.
use hylo::algebra::{Boolean, Tropical};
use hylo::path::{closure, relax, Fifo, Graph, ShortestFirst};
use hylo::sort::{insertion_sort, mergesort, quicksort, selection_sort};

struct Lcg(u64);
impl Lcg { fn next(&mut self) -> u64 { self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); self.0 >> 33 } }

#[test]
fn four_sorts_agree_with_std() {
    let mut r = Lcg(7);
    for n in 0..60 {
        let v: Vec<i64> = (0..n).map(|_| (r.next() % 20) as i64).collect();
        let mut want = v.clone(); want.sort();
        assert_eq!(insertion_sort(v.clone()), want);
        assert_eq!(selection_sort(v.clone()), want);
        assert_eq!(quicksort(v.clone()), want);
        assert_eq!(mergesort(v.clone()), want);
    }
}

fn random_graph(seed: u64, n: usize) -> Graph<Tropical> {
    let mut r = Lcg(seed);
    let mut adj = Vec::new();
    for _ in 0..n {
        let mut es = Vec::new();
        for v in 0..n { if r.next().is_multiple_of(3) { es.push((v, Tropical(1 + r.next() % 9))); } }
        adj.push(es);
    }
    Graph { adj }
}

fn brute(g: &Graph<Tropical>, s: usize) -> Vec<u64> {
    // Bellman-Ford by textbook, n rounds of full relaxation.
    let n = g.adj.len();
    let mut d = vec![u64::MAX; n]; d[s] = 0;
    for _ in 0..n { for u in 0..n { if d[u] != u64::MAX { for &(v, w) in &g.adj[u] { d[v] = d[v].min(d[u] + w.0); } } } }
    d
}

#[test]
fn bellman_ford_dijkstra_floyd_warshall_agree() {
    for seed in 0..40 {
        let g = random_graph(seed, 9);
        let want = brute(&g, 0);
        let bf: Vec<u64> = relax::<Tropical, Fifo>(&g, 0).iter().map(|t| t.0).collect();
        let dj: Vec<u64> = relax::<Tropical, ShortestFirst<Tropical>>(&g, 0).iter().map(|t| t.0).collect();
        let fw: Vec<u64> = closure(g.matrix())[0].iter().map(|t| t.0).collect();
        assert_eq!(bf, want, "seed {seed}");
        assert_eq!(dj, want, "seed {seed}");
        assert_eq!(fw, want, "seed {seed}");
    }
}

#[test]
fn reachability_is_the_same_plan_over_boolean() {
    for seed in 0..40 {
        let g = random_graph(seed, 9);
        let gb = Graph { adj: g.adj.iter().map(|es| es.iter().map(|&(v, _)| (v, Boolean(true))).collect()).collect() };
        let want: Vec<bool> = brute(&g, 0).iter().map(|&d| d != u64::MAX).collect();
        let got: Vec<bool> = relax::<Boolean, Fifo>(&gb, 0).iter().map(|b| b.0).collect();
        let warshall: Vec<bool> = closure(gb.matrix())[0].iter().map(|b| b.0).collect();
        assert_eq!(got, want, "seed {seed}");
        assert_eq!(warshall, want, "seed {seed}");
    }
}

#[test]
fn counting_paths_needs_the_acyclic_plan() {
    use hylo::algebra::Nat;
    use hylo::path::relax_acyclic;
    let mut r = Lcg(11);
    for _ in 0..40 {
        let n = 8;
        // edges only forward: a DAG by construction
        let mut adj = Vec::new();
        for u in 0..n { let mut es = Vec::new(); for v in u + 1..n { if r.next().is_multiple_of(2) { es.push((v, Nat(1))); } } adj.push(es); }
        let g = Graph { adj };
        let got = relax_acyclic(&g, 0).expect("acyclic");
        // brute: count paths by DFS enumeration
        fn count(g: &Graph<Nat>, u: usize, t: usize) -> u64 { if u == t { 1 } else { g.adj[u].iter().map(|&(v, _)| count(g, v, t)).sum() } }
        for (t, g_t) in got.iter().enumerate() { assert_eq!(g_t.0, count(&g, 0, t)); }
    }
    // a cycle makes the acyclic plan refuse, instead of miscounting
    let cyc = Graph { adj: vec![vec![(1, Nat(1))], vec![(0, Nat(1))]] };
    assert!(relax_acyclic(&cyc, 0).is_none());
}

#[test]
fn n_queens_is_global_search_over_two_semirings() {
    use hylo::algebra::Nat;
    use hylo::search::{search, Queens};
    for (n, want) in [(4, 2), (5, 10), (6, 4), (7, 40), (8, 92)] {
        assert_eq!(search::<Queens, Nat>(&Queens, &n).0, want);
        assert!(search::<Queens, Boolean>(&Queens, &n).0);
    }
    assert!(!search::<Queens, Boolean>(&Queens, &3).0);
}
