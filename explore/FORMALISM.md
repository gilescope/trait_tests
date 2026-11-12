# A formalism for parameterised algorithms

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

In `formalism/verify/FormalismVerify/Spec.lean` (statements only so far):

1. `eval_eq_measure` (Lemma 1): evaluation in any commutative semiring equals the measure
   of the expression's semantics.
2. `Delta` is a `CommSemiring` (Theorem 3), `Delta D1 D2` is a `Dioid` (Theorem 4).
3. `solve_sound` (Claim 1 at the root): the DP output denotes exactly the solution set,
   given an `Instance` that discharges the trace obligations.

Then an instance owes only its trace obligations, and a semiring owes only its laws.
Everything else is inherited.

## What is tested, and why tests remain

- Semiring and dioid laws: `laws.rs` via `trait_tests`, one `#[test]` per law per
  implementor. These are the executable twin of the Lean class axioms. An implementor with
  a Lean instance does not need them; one without does.
- Oracle tests (`tests/hcol_oracle.rs`): for random valid decompositions, the expression's
  set semantics equals brute force, and each semiring's evaluation equals the brute-force
  answer to its question. These are the tests the Lean theorems will make redundant.
- Tests still earn their place for what is not modelled: arithmetic overflow policy,
  the validator, and the bridge between extracted and hand-written definitions.

## Verification pipeline

`earthly +verify`: `charon cargo --preset=aeneas` turns the crate into LLBC,
`aeneas -backend lean` turns LLBC into `Extracted/*.lean`, `lake build` checks
`Spec.lean` against it. The core modules are written in Aeneas's subset: `no_std` +
`alloc`, no closures, no iterator adaptors, no hash maps, index loops, no `&mut` through
generics. `semantics` (the set-theoretic oracle) and `laws` are outside that subset and
are feature-gated out of extraction.

Status: pipeline unexecuted. This container has no Docker daemon and the Lean installer
was blocked, so `Spec.lean` has not been elaborated. Expect name and tactic fixes on the
first `lake build`.

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
