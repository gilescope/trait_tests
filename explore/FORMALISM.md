# A formalism for algorithms

Current statement (see the research note "Interlocking Traits" for the evidence):

```
algorithm = hylo(plan, algebra) over a shape
  Shape   F : one layer of the virtual structure, owned (no lifetime GATs)
  Plan    c : A → F A, a type with state; obligation: recursive (Knuth's finiteness)
  Algebra a : F B → B, a type; obligation: the carrier's laws
  Query     : the choice of a; free by fusion
```

Two theorems are the generic API: **fusion** (an algebra homomorphism commutes with the hylo,
so the query is free) and the **homomorphism theorem** (with a commutative monoid action and
the shape's laws, the plan is free). Lean statements: `formalism/verify/FormalismVerify/Hylo.lean`.
Implementation: `hylo/`. Named algorithms are pairs:

| Knuth | name | shape | plan | algebra |
|---|---|---|---|---|
| 4.5.2 | gcd | `IterF` | `Euclid` | `Last` |
| 4.6.3 | power, Fibonacci | `IterF` | `Square` over a monoid | `Last` |
| 4.6 | reduce, scan | `ListF` / `LeafTreeF` | `Uncons` / `Halve` | `ReduceL` / `ReduceT` / `Scan` |
| 5.2.1 | insertion sort | `ListF` | `Uncons` | `Insert` |
| 5.2.3 | selection sort | `ListF` | `SelectMin` | `Cons` |
| 5.2.2 | quicksort | `NodeTreeF` | `Pivot` | `Concat` |
| 5.2.4 | mergesort | `LeafTreeF` | `Halve` | `Merge` |
| 6.2.1 | binary search, count | `RoseF` | `Backtrack<BinarySearch>` | `Aggregate<Boolean / Nat>` |
| 7.2.2 | backtracking, N-queens | `RoseF` | `Backtrack<Queens>` | `Aggregate<S>` |
| 7.3 | Bellman-Ford | `IterF` | `Relax<Tropical, Fifo>` | `Last` |
| 7.3 | Dijkstra | `IterF` | `Relax<Tropical, ShortestFirst>` | `Last` |
| 7.3 | path counting (DAG) | `IterF` | `Relax<Nat, Topological>` | `Last` |
| 7.3 | Floyd–Warshall, Warshall | `IterF` | `Lehmann` over `Star` | `Last` |
| 7.8 | branch and bound, knapsack | `RoseF` | `BranchBound<Knapsack>` | `Best` |

Bounds are theorem hypotheses: `KClosed<0>` on `relax` (Mohri Thm 1), `Superior` on
`ShortestFirst` (Huang), `Star` on `Lehmann` (Lehmann), `Monoid` on reduce (third homomorphism
theorem). `Nat` has no `KClosed` impl, so counting on a cyclic graph does not compile; the
acyclic plan is `relax_acyclic`, which refuses cycles at runtime.

The rest of this file is the earlier, narrower formalism (the semiring DP of Baril et al.),
which is now one instance: `trace_dp` is a hylo over a decomposition shape whose algebra is a
semiring measure.

---

# The semiring DP instance

After Baril, Couceiro, Lagerkvist, *New perspectives on semiring applications to dynamic
programming*, Discrete Applied Mathematics 383 (2026), arXiv:2512.03916.

## The claim

An algorithm for an NP problem with certificates is three independent things:

| Layer | Paper | Rust | Lean obligation |
|---|---|---|---|
| **Construction**: how the input is built | nice tree decomposition, k-expression | `scheme::Node<Op>`, validated by an instance (`hcol::NiceTd::new`) | none: validation is executable, `Node` carries no invariant |
| **Trace**: finite summary of a partial candidate, compositional under construction | Remark 3 (three conditions) | `scheme::Traced::{step, accept}` | per instance: `Instance.accept_iff`, `step_sound` |
| **Algebra**: which question | commutative semiring + measure matrix | `semiring::Semiring`, `expr::Measure` | per semiring: `CommSemiring` instance |

The scheme itself, `scheme::run`, is written once. It does not know what a semiring is.
It outputs a **join/union expression** (`expr::Expr`) of the solution set. Choosing the
algebra happens after the algorithm has run:

| Semiring | Measure | Computes |
|---|---|---|
| `Boolean` | all ones | decision |
| `Nat` (Z/2^64) | all ones | count |
| `Tropical` (min, +) | cost table | optimum |
| `Delta<Tropical, Nat>` | `(cost, 1)` | number of optima (Theorem 6) |
| `Boolean` | allowed-value table | list version |

Bound: `f(parameter) · poly(n)` is the number of traces per node times `n`. The expression
size is the same bound; `expr::eval` is linear in it (Lemma 1).

## What is correct by construction

- **Legality of `⊎`.** The paper's expressions can FAIL (union of overlapping sets).
  `scheme::run` only unions expressions that land on the same trace from *different* child
  rows, and rows have distinct traces. Disjointness is a consequence of trace condition 3,
  so the Rust never checks it and never needs to.
- **Legality of `⨝`.** Joins combine expressions over disjoint owned-variable sets. Owned
  variables are assigned exactly once (`Invalid::Owners`), so domains are disjoint.
- **The Δ-set invariant.** `Delta::new` normalises `(d, a)` to `(d, 0)` when `d` is not
  regular. No value outside `D Δ A` can exist.
- **Only validated constructions run.** `hcol::solve` takes a `NiceTd`, which exists only
  if Lemma 2's conditions and unique ownership held.

## What is proved once, for every instance

In `formalism/verify/FormalismVerify/Spec.lean` (all proved, checked in CI):

1. `eval_eq_measure` (Lemma 1): evaluation in any commutative semiring equals the measure
   of the expression's semantics.
2. `Delta` is a `CommSemiring` (Theorem 3), `Delta D1 D2` is a `Dioid` (Theorem 4).
3. `solve_sound` (Claim 1 at the root): on a well-formed construction (`Instance.WF`), the
   DP output denotes exactly the solution set, given an `Instance` that discharges the trace
   obligations. `Bits.lean` discharges them for one instance (bit assignments with `k` ones),
   so there `Bits.solve_sound` holds with no hypothesis beyond well-formedness.
4. `solve_sound_extracted` (`RefineRun.lean`): the same, about the Rust. The Aeneas extraction
   of `expr.rs` and `scheme.rs` computes the model function by function (`Refine.lean`:
   `union`, `join`, `join_leaves`, `union_into`; `RefineStep.lean` with `Odometer.lean`:
   `step_node` and its odometer over the children's rows; `RefineRun.lean`: `run`, `solve`),
   so `scheme::solve` succeeds and its expression denotes the solution set, given that the
   extracted construction is the model's (`NodeRel`), every table built fits a `Vec` (`Fits`,
   the one way `step_node` can fail) and the instance's extracted `step`/`accept` compute the
   model's (`TracedSpec`, stated through a representation `Repr`: how the Rust's operation
   and trace types read back as the model's).
5. `BitsRust.solve_bits_sound` (`BitsRust.lean`): Claim 1 for a Rust instance end to end.
   `instances/bits.rs` implements `Traced` with a `u64` count of ones summed by wrapping
   addition; read through `Repr` (`U64.val` on traces), it is the model instance
   `Bits.inst (Bits.modular U64.size)`, whose trace is the count modulo `2^64`.
   `BitsRust.tracedSpec` proves its `TracedSpec` (the sum loop, `step`, `accept`, and `u64`'s
   `PartialEq`/`Clone`), so the extracted `hylo::dp::solve_bits` denotes exactly the
   assignments with `k` ones modulo `2^64`, for a tree with distinct leaves whose tables fit.
   `Bits.lean`'s model is parameterised by a `Counter` (exact, or modular `M`) for this.
6. `trace_dp_sound_extracted` (`RefineHylo.lean`): Claim 1 for `hylo::dp::trace_dp`, the
   trace DP written as the rose hylomorphism of `hylo` (`hylo_rose` pops the children off
   the back, runs each, reverses the results and folds the layer with `step_node`;
   `trace_dp` reverses the root table and pops its accepted rows into a union). Read through
   `Repr` it computes `Traced.solve` too (`trace_dp_spec`), under the same hypotheses as
   `scheme::solve`. This needed a model of `Vec::pop` in the Aeneas library (the fork has
   one now); without it Aeneas emits an axiom for `pop` and nothing can be proved about a
   function that calls it.

Then an instance owes only its trace obligations, and a semiring owes only its laws.
Everything else is inherited.

## What is tested, and why tests remain

- Semiring and dioid laws: `laws.rs` via `trait_tests`, one `#[test]` per law per
  implementor. These are the executable twin of the Lean class axioms. An implementor with
  a Lean instance does not need them; one without does.
- Oracle tests (`tests/hcol_oracle.rs`, `tests/bits_oracle.rs`): for random valid
  decompositions (and small bit trees), the expression's set semantics equals brute force, and
  each semiring's evaluation equals the brute-force answer to its question. These are the tests
  the Lean theorems make redundant; for `Bits` they already are, up to the `Fits` hypothesis.
- Tests still earn their place for what is not modelled: arithmetic overflow policy,
  the validator, and the bridge between extracted and hand-written definitions.

## Verification pipeline

`earthly +verify`: `charon cargo --preset=aeneas` turns the crate into LLBC,
`aeneas -backend lean` turns LLBC into `Extracted/*.lean`, `lake build` checks
`Spec.lean` and the refinement against it. Charon translates only the signatures of a
dependency crate unless told otherwise, so the `formalism` bodies are asked for with
`--include=formalism::expr::_ --include=formalism::scheme::_ --include=formalism::instances::bits::_`,
and `scheme::solve` is reached through `hylo::dp::solve_scheme` and `hylo::dp::solve_bits` (a
start item in a dependency is dropped). The core modules are written in Aeneas's subset: `no_std` +
`alloc`, no closures, no iterator adaptors, no hash maps, index loops, no `&mut` through
generics. `semantics` (the set-theoretic oracle) and `laws` are outside that subset and
are feature-gated out of extraction.

Status (17 November 2026): green end to end on the gilescope/aeneas release tarball
`build-4797bb9` (GAT-lite plus the `Vec::pop` model, Lean 4.34.0). `earth +verify` extracts
`explore/hylo` from the sixteen named algorithms and the `solve`/`trace_dp` roots (3766 lines of
Lean, snapshot in `hylo/extracted/`), then `lake build` checks `Spec.lean`, `Hylo.lean`, the
extracted module and the refinement.
Every theorem is proved, no `sorry` remains: `fusion`, `reduce_eq_prod`, `scan_eq_prefixes` (the
homomorphism theorem for both sequence shapes), `eval_eq_measure` (Lemma 1), the Δ-product
semiring instance (Theorem 3, with `regular` = cancellative) and `solve_sound` (Claim 1: the
trace DP, modelled constructor for constructor after `scheme.rs`, denotes exactly the solution
set). Claim 1 is conditional on the `Instance` obligations stated in `Spec.lean`, which are
relative to a well-formedness predicate `WF` (quantifying them over every list of children was
unsatisfiable, since a tree may repeat a variable; the paper's decompositions are well formed by
construction): one domain per well-formed node, children own disjoint variables, `step` yields
each output's leaves once, `cand_iff` and `trace_mk`. `Bits.lean` discharges every obligation
for a concrete instance (leaves assign one bit each, the trace is the number of ones, a solution
has exactly `k` ones, `WF` = distinct leaves), so `Bits.solve_sound` is an unconditional
corollary for well-formed trees. The refinement (`Refine.lean`, `Odometer.lean`,
`RefineStep.lean`, `RefineRun.lean`, all proved) relates the extracted `expr.rs` and `scheme.rs`
to the model and transfers Claim 1 to the Rust (`solve_sound_extracted`); until this step the
extracted `step_node` and `union` were axioms, because Charon keeps a dependency's bodies opaque
by default. `Spec.stepNode` enumerates child-row tuples in the Rust's odometer order (`tuples`)
so that the refinement is syntactic. `BitsRust.lean` closes the loop for one Rust instance:
`solve_bits_sound` is Claim 1 about the extracted `hylo::dp::solve_bits`, with the `u64`
wrapping count read as the model's modular counter. `RefineHylo.lean` does the same for the
hylomorphism form, `hylo::dp::trace_dp` (`trace_dp_sound_extracted`).
Upstream Aeneas main (1dc8ad3) fails on the same crate: with the `formalism` bodies included
its newer loop encoding makes Aeneas itself crash (`[Error] Internal error`); before that it
produced Lean that did not compile (universe mismatch on the generic `hylo_rose_loop0`,
duplicate pattern binders). The fork does not have that problem. GAT-lite (`gilescope/aeneas` PR #7,
draft) is green on the fork's full test suite, including the GAT test's generated Lean.

A push to this branch gets its Lean verdict in about four minutes: the Earthfile layers for
Mathlib and the Aeneas backend are cached in GHCR per Aeneas revision, only the three proof
files rebuild.

## What fits, what does not

Fits: every problem with a construction grammar and a compositional trace of bounded
cardinality. The paper does Connected Dominating Set (clique-width), CSP and H-colouring
(tree-width). This crate has H-colouring; Connected Dominating Set over k-expressions is
the natural second instance (`Op` with four constructors, trace = signature + domination).

Does not fit as stated: problems whose solution sets have no polynomial-size join/union
expression (permutations unless P = #P, Hamiltonian cycles unless P = NP; Theorems 1–2).
Problems needing subtraction need the ring extension (Section 5.1 remark). Problems that
are not "set of certificates" shaped, such as sorting from `algo_std`, are folds over a
construction too, but their algebra is not a semiring measure and they get no free
counting/optimisation; they belong to a sibling formalism, not this one.
