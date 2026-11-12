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

#[test]
fn knapsack_branch_and_bound_matches_dp() {
    use hylo::search::{maximise, Knapsack};
    let mut r = Lcg(23);
    for _ in 0..60 {
        let n = 1 + (r.next() % 12) as usize;
        let items: Vec<(u64, u64)> = (0..n).map(|_| (1 + r.next() % 15, 1 + r.next() % 30)).collect();
        let capacity = r.next() % 40;
        // textbook DP oracle
        let mut dp = vec![0u64; capacity as usize + 1];
        for &(w, v) in &items { for c in (w as usize..=capacity as usize).rev() { dp[c] = dp[c].max(dp[c - w as usize] + v); } }
        let k = Knapsack { items, capacity };
        assert_eq!(maximise(&k, &()), dp[capacity as usize]);
    }
}

#[test]
fn reduce_is_plan_independent_and_scan_matches_prefix_sums() {
    use hylo::algebra::Sum;
    use hylo::seq::{reduce_par, reduce_seq, scan};
    let mut r = Lcg(31);
    for n in 0..40 {
        let v: Vec<Sum> = (0..n).map(|_| Sum(r.next() % 100)).collect();
        let total = Sum(v.iter().map(|s| s.0).sum());
        assert_eq!(reduce_seq(v.clone()), total);   // ListF plan
        assert_eq!(reduce_par(v.clone()), total);   // LeafTreeF plan: third homomorphism theorem
        let mut acc = 0; let want: Vec<Sum> = v.iter().map(|s| { acc += s.0; Sum(acc) }).collect();
        assert_eq!(scan(v), want);
    }
}

#[test]
fn euclid_and_repeated_squaring() {
    use hylo::algebra::{Mat2, Sum};
    use hylo::num::{gcd, power};
    assert_eq!(gcd(48u64, 18), 6);
    assert_eq!(gcd(17u64, 5), 1);
    assert_eq!(gcd(0u64, 9), 9);
    assert_eq!(power(Sum(3), 7), Sum(21));                 // additive monoid: multiplication by squaring
    let fib = |n: u64| power(Mat2([[1, 1], [1, 0]]), n).0[0][1];
    assert_eq!((0..12).map(fib).collect::<Vec<_>>(), [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]);
}

#[test]
fn binary_search_counts_with_nat_and_decides_with_boolean() {
    use hylo::algebra::Nat;
    use hylo::search::{search, BinarySearch};
    let mut r = Lcg(37);
    for n in 0..40 {
        let mut v: Vec<u64> = (0..n).map(|_| r.next() % 10).collect();
        v.sort();
        for t in 0..10 {
            let want = v.iter().filter(|&&x| x == t).count() as u64;
            let bs = BinarySearch { sorted: &v, target: t };
            assert_eq!(search::<_, Nat>(&bs, &()).0, want);
            assert_eq!(search::<_, Boolean>(&bs, &()).0, want > 0);
        }
    }
}

#[test]
fn trace_dp_is_the_formalism_crate_as_one_pair() {
    use formalism::expr::{eval, Ones};
    use formalism::instances::hcol::{h, solve, Graph as HG, HColoring, NiceTd, Op};
    use formalism::scheme::Node;
    use hylo::dp::trace_dp;
    // Path 0-1-2 with a hand-built nice tree decomposition: bags {0,1} then {1,2}.
    let mut g = HG::new(3); g.add_edge(0, 1); g.add_edge(1, 2);
    let n = |op, children| Node { op, children };
    let td = n(Op::Forget { v: 2 }, vec![n(Op::Forget { v: 1 }, vec![n(Op::Introduce { v: 2, owner: true }, vec![
        n(Op::Forget { v: 0 }, vec![n(Op::Introduce { v: 1, owner: true }, vec![n(Op::Introduce { v: 0, owner: true }, vec![n(Op::Leaf, vec![])])])])])])]);
    let p = HColoring { g: g.clone(), h: h::independent_set() };
    let reference = solve(&p, &NiceTd::new(&g, &td).unwrap());
    let as_hylo = trace_dp(&p, td.clone());
    assert_eq!(as_hylo, reference);
    // The query is fusion: same expression, two measures. P3 has 5 independent sets.
    assert_eq!(eval::<formalism::semiring::Nat, _>(&as_hylo, &Ones).0, 5);
    assert!(eval::<formalism::semiring::Boolean, _>(&as_hylo, &Ones).0);
}

#[test]
fn counting_optima_is_a_query_and_forbids_cutting_ties() {
    use hylo::algebra::{Delta, Nat, Tropical};
    use hylo::search::{maximise_count, search, Knapsack, Queens};
    // N-queens: minimum column sum and how many placements reach it, vs brute force over all solutions.
    for n in 4..=7usize {
        let d: Delta<Tropical, Nat> = search(&Queens, &n);
        let all = { // every solution's cost, by naive recursion
            fn go(n: usize, cols: &mut Vec<usize>, out: &mut Vec<u64>) {
                if cols.len() == n { out.push(cols.iter().map(|&c| c as u64).sum()); return; }
                for c in 0..n { let r = cols.len(); if cols.iter().enumerate().all(|(i, &ci)| ci != c && (r - i) != c.abs_diff(ci)) { cols.push(c); go(n, cols, out); cols.pop(); } }
            }
            let mut v = Vec::new(); go(n, &mut Vec::new(), &mut v); v
        };
        let best = *all.iter().min().unwrap();
        assert_eq!(d.cost().0, best);
        assert_eq!(d.count().0, all.iter().filter(|&&c| c == best).count() as u64);
    }
    // Knapsack: (optimum, number of optimal subsets) vs a counting DP.
    let mut r = Lcg(41);
    for _ in 0..60 {
        let n = 1 + (r.next() % 10) as usize;
        let items: Vec<(u64, u64)> = (0..n).map(|_| (1 + r.next() % 8, 1 + r.next() % 6)).collect(); // small values: many ties
        let capacity = r.next() % 20;
        let mut dp: Vec<(u64, u64)> = vec![(0, 1); capacity as usize + 1]; // (best, count)
        for &(w, v) in &items {
            for c in (w as usize..=capacity as usize).rev() {
                let (b, k) = dp[c - w as usize];
                let cand = (b + v, k);
                if cand.0 > dp[c].0 { dp[c] = cand } else if cand.0 == dp[c].0 { dp[c].1 += cand.1 }
            }
        }
        // dp[capacity] counts subsets with weight <= capacity achieving the best: that is what the search counts
        let k = Knapsack { items, capacity };
        assert_eq!(maximise_count(&k, &()), dp[capacity as usize]);
    }
}

#[test]
fn generic_gat_hylo_still_runs_every_pair_through_the_bridges() {
    use hylo::hylo;
    use hylo::shape::{LeafTreeF, ListF, NodeTreeF};
    use hylo::sort::{Concat, Halve, Insert, Merge, Pivot, Uncons};
    let v: Vec<i64> = vec![5, 3, 9, 1, 3, 7];
    let mut want = v.clone(); want.sort();
    assert_eq!(hylo::<ListF<i64>, _, _>(&mut Uncons, &mut Insert, v.clone()), want);
    assert_eq!(hylo::<NodeTreeF<i64>, _, _>(&mut Pivot, &mut Concat, v.clone()), want);
    assert_eq!(hylo::<LeafTreeF<i64>, _, _>(&mut Halve, &mut Merge, v), want);
}
