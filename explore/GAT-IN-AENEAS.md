# GATs in Aeneas: how hard, and what it buys

Full note: https://claude.ai/artifact/LgL4QU15f6SbBKpLL6P63r (15 November 2026, from reading
gilescope/aeneas at 7a8e111 and AeneasVerif/charon at c3baf87).

**Verdict.** GAT-lite (type parameters only; no lifetimes, bounds or where-clauses) is a medium,
Aeneas-only project: ~600–800 lines of OCaml across seven files plus one Lean test. Charon already
represents GATs fully (binder on decl/impl types, args on `TTraitType` and `ItemClause`) and, under
`--preset=aeneas`, lifts ordinary associated types into trait type parameters while leaving GATs in
place. Aeneas rejects the residual GAT at four `generics = empty` asserts in
`SymbolicToPureTypes.ml` (183, 391, 532, 669), one `ItemClause` raise (129), and the trait decl
assert in `SymbolicToPure.ml` (232–236).

**Route.** Residual field: `structure Shape (Self : Type) where Layer : Type → Type; map : …`.
The alternative, a higher-kinded lifted parameter, needs a Charon change too.

| # | Item | Files | Size |
|---|---|---|---|
| 1 | Pure AST: args on `TTraitType`, binders on decl/impl `types`, a type lambda | `pure/Pure.ml`, `PrintPure.ml` | ~80 |
| 2 | Translate GAT args at the four assert sites; `ItemClause` under GAT-lite | `symbolic/SymbolicToPureTypes.ml` | ~80 |
| 3 | Keep residual types with binders in decl/impl translation | `symbolic/SymbolicToPure.ml` | ~80 |
| 4 | Extraction: kinded field, lambda impl value, applied projection `Inst.Layer A` | `extract/Extract*.ml` | ~200 |
| 5 | Constraint rewriting compares args | `PrePasses.ml` | ~15 |
| 6 | Normalise `<ListF as Shape>::Layer<u32>` through known impls | new pass or Charon | ~150 |
| 7 | `tests/src/gat.rs`, `lean_lib Gat`; land as known-failure first | `tests/` | small |

**What it does not unblock.** The generic `hylo` also hits mixed recursive groups (Aeneas #1264,
independent) and `partial_fixpoint` monotonicity through the abstract `map` method, which has no
automatic answer: fuel, a decreases clause, or a monotonicity law on `Shape`. So the per-shape core
stays the verified core; GAT support widens what extracts; the generic scheme is proved by hand on
the Lean model.

**Recommendation.** Do GAT-lite in the fork as a PR series following the table; steps 1–3 alone
turn the `CFailure` crash into a clear error (upstream #1195). Offer upstream once green (#1112).

## Status (15 November 2026)

Done in the fork (`gilescope/aeneas`, branch `gat-lite`, draft PR #7), items 1–5 and 7 of the
table; item 6 was not needed, Charon normalises the projection through known impls already.
Two fixes beyond the plan were needed and found by the acceptance test, not by inspection:

* `make_subst_from_generics` mapped `Self` to `UnknownTrait` when re-binding a method
  signature; plain associated types never left a `Self` projection in a signature, a GAT does
  (`Self::Layer<X>`), and every method mentioning it extracted as `sorry`.
* Impl methods printed their binders with the impl's explicit-info, computed without inputs,
  while the trait field used the declaration's, computed from them: `fn wrap<X>(x: X)` read
  `forall {X}` on one side and `fun (X : Type)` on the other. Pre-existing; no earlier test had a
  method type parameter that appears only in an input.

The fork CI (tidiness, `nix build`, the regenerated test diff, and Lean compiling every test
including `Gat.lean`) is green on `b2a7475`. Release tarballs: `build-1977b47` (before the
binder fix) and the one cut from `release/gat-lite` at `74561b7`. Nothing has been offered
upstream.
