import FormalismVerify.RefineStep

/-!
# Refinement of `scheme::run` and `scheme::solve`, and Claim 1 about the Rust

`run` folds `step_node` over the construction, `solve` unions the accepted root rows. With
`step_node` refined (`RefineStep.lean`), both compute the model's `Traced.run` and
`Traced.solve`, and `solve_sound` (Claim 1, `Spec.lean`) transfers to the extracted code:
`solve_sound_extracted`.

Two side conditions are the Rust's own: the construction the extracted code gets must be the
model's (`NodeRel`), and every table built along the way must fit a `Vec` (`Fits`, the only
way `step_node` can fail).
-/

namespace Formalism.Refine
open Aeneas Aeneas.Std Result hylo Odometer

section Run
variable {P Op Tau : Type} [DecidableEq Tau]

mutual
/-- The extracted construction is the model's. -/
def NodeRel : formalism.scheme.Node Op → Node Op → Prop
  | .mk op cs, .mk op' ms => op = op' ∧ NodeRelList cs.val ms
def NodeRelList : List (formalism.scheme.Node Op) → List (Node Op) → Prop
  | [], [] => True
  | c :: cs, m :: ms => NodeRel c m ∧ NodeRelList cs ms
  | [], _ :: _ => False
  | _ :: _, [] => False
end

theorem NodeRelList.length_eq :
    ∀ {cs : List (formalism.scheme.Node Op)} {ms : List (Node Op)}, NodeRelList cs ms →
      cs.length = ms.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [NodeRelList])
  | _ :: _, [], h => absurd h (by simp [NodeRelList])
  | _ :: cs, _ :: ms, h => by
    rw [NodeRelList] at h
    simp only [List.length_cons, NodeRelList.length_eq h.2]

theorem NodeRelList.getElem :
    ∀ {cs : List (formalism.scheme.Node Op)} {ms : List (Node Op)}, NodeRelList cs ms →
      ∀ (j : ℕ) (h₁ : j < cs.length) (h₂ : j < ms.length), NodeRel cs[j] ms[j]
  | [], _, _, _, h₁, _ => absurd h₁ (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, h₂ => absurd h₂ (Nat.not_lt_zero _)
  | _ :: _, _ :: _, h, 0, _, _ => by
    rw [NodeRelList] at h
    exact h.1
  | _ :: _, _ :: _, h, j + 1, h₁, h₂ => by
    rw [NodeRelList] at h
    exact NodeRelList.getElem h.2 j (by simpa using h₁) (by simpa using h₂)

mutual
/-- Every table the model builds under a node fits a `Vec`: the one precondition of the
    extracted `step_node`. -/
def Fits (I : Traced Op Tau) : Node Op → Prop
  | .mk op cs => (Traced.stepNode I op (Traced.runList I cs)).length < Usize.max ∧ FitsList I cs
def FitsList (I : Traced Op Tau) : List (Node Op) → Prop
  | [] => True
  | c :: cs => Fits I c ∧ FitsList I cs
end

theorem runList_length (I : Traced Op Tau) :
    ∀ ms : List (Node Op), (Traced.runList I ms).length = ms.length
  | [] => rfl
  | _ :: ms => by
    rw [Traced.runList, List.length_cons, List.length_cons, runList_length I ms]

theorem runList_append (I : Traced Op Tau) :
    ∀ ms₁ ms₂ : List (Node Op),
      Traced.runList I (ms₁ ++ ms₂) = Traced.runList I ms₁ ++ Traced.runList I ms₂
  | [], _ => by rw [List.nil_append, Traced.runList, List.nil_append]
  | m :: ms₁, ms₂ => by
    rw [List.cons_append, Traced.runList, Traced.runList, runList_append I ms₁ ms₂,
      List.cons_append]

/-! ## `run`: the children first -/

theorem run_loop_spec (inst : formalism.scheme.Traced P Op Tau) (p : P)
    (I : Traced Op Tau) (nop : Op) (ncs : alloc.vec.Vec (formalism.scheme.Node Op))
    (op : Op) (ms : List (Node Op)) (hrel : NodeRel (.mk nop ncs) (.mk op ms))
    (hIH : ∀ (j : ℕ) (hj : j < ms.length) (n' : formalism.scheme.Node Op), NodeRel n' ms[j] →
      formalism.scheme.run inst p n' ⦃ (t : alloc.vec.Vec (formalism.scheme.Row Tau)) =>
        tableOf t = Traced.run I ms[j] ⦄)
    (child_tables : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau))) (c : Usize)
    (hc : c.val ≤ ncs.val.length)
    (htabs : tablesOf child_tables = Traced.runList I (ms.take c.val)) :
    formalism.scheme.run_loop inst p (.mk nop ncs) child_tables c
      ⦃ (op' : Op) (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau))) =>
        op' = op ∧ tablesOf cts = Traced.runList I ms ⦄ := by
  rw [NodeRel] at hrel
  obtain ⟨hop, hrel⟩ := hrel
  have hlen : ncs.val.length = ms.length := hrel.length_eq
  unfold formalism.scheme.run_loop
  apply loop.spec_decr_nat (measure := fun s => ncs.val.length - s.2.val)
    (inv := fun s => s.2.val ≤ ncs.val.length ∧ tablesOf s.1 = Traced.runList I (ms.take s.2.val))
  · rintro ⟨cts1, c1⟩ ⟨hc1, htabs1⟩
    replace hc1 : c1.val ≤ ncs.val.length := hc1
    replace htabs1 : tablesOf cts1 = Traced.runList I (ms.take c1.val) := htabs1
    unfold formalism.scheme.run_loop.body
    simp only [alloc.vec.Vec.index_slice_index, formalism.scheme.Node.children._simpLemma_,
      formalism.scheme.Node.op._simpLemma_]
    split
    · rename_i hlt
      have hlt' : c1.val < ncs.val.length := by scalar_tac
      have hlt'' : c1.val < ms.length := by rw [← hlen]; exact hlt'
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec ncs c1 hlt')
      intro n hn
      replace hn : n = ncs.val[c1.val] := hn
      apply WP.spec_bind (hIH c1.val hlt'' n (by rw [hn]; exact hrel.getElem c1.val hlt' hlt''))
      intro v hv
      replace hv : tableOf v = Traced.run I ms[c1.val] := hv
      have hcts1 : cts1.val.length < Usize.max := by
        have : (tablesOf cts1).length = c1.val := by
          rw [htabs1, runList_length, List.length_take]
          exact Nat.min_eq_left hlt''.le
        rw [length_tablesOf] at this
        scalar_tac
      apply WP.spec_bind (alloc.vec.Vec.push_spec cts1 v hcts1)
      intro cts2 hcts2
      replace hcts2 : cts2.val = cts1.val ++ [v] := hcts2
      apply WP.spec_bind (Usize.add_spec (x := c1) (y := 1#usize) (by scalar_tac))
      intro c2 hc2
      replace hc2 : c2.val = c1.val + (1#usize).val := hc2
      have hc2' : c2.val = c1.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      rw [tablesOf, hcts2, List.map_append, hc2', List.take_succ_eq_append_getElem hlt'',
        runList_append, Traced.runList, Traced.runList, ← hv]
      rw [tablesOf] at htabs1
      rw [htabs1]
      rfl
    · rename_i hge
      have htake : ms.take c1.val = ms := List.take_of_length_le (by rw [← hlen]; scalar_tac)
      simp only [WP.spec_ok, WP.uncurry'_pair]
      rw [htabs1, htake]
      exact ⟨hop, rfl⟩
  · exact ⟨hc, htabs⟩

mutual
/-- `scheme::run` computes the model's `run`. -/
theorem run_spec (inst : formalism.scheme.Traced P Op Tau) (p : P) (I : Traced Op Tau)
    (hI : TracedSpec inst p I) :
    ∀ (m : Node Op) (node : formalism.scheme.Node Op), NodeRel node m → Fits I m →
      formalism.scheme.run inst p node ⦃ (t : alloc.vec.Vec (formalism.scheme.Row Tau)) =>
        tableOf t = Traced.run I m ⦄
  | .mk op ms, .mk nop ncs, hrel, hfit => by
    rw [Fits] at hfit
    obtain ⟨hfin, hfits⟩ := hfit
    unfold formalism.scheme.run
    apply WP.spec_bind (run_loop_spec inst p I nop ncs op ms hrel
      (fun j hj n' hrel' => run_specList inst p I hI ms hfits j hj n' hrel')
      (alloc.vec.Vec.new _) 0#usize (by scalar_tac) (by simp [tablesOf, alloc.vec.Vec.new, Traced.runList]))
    rintro ⟨t, cts⟩ hp
    have hp' : t = op ∧ tablesOf cts = Traced.runList I ms := hp
    obtain ⟨ht, hcts⟩ := hp'
    subst t
    try dsimp only
    apply WP.spec_mono (step_node_spec inst p I hI op cts (by rw [hcts]; exact hfin))
    intro t' ht'
    rw [ht', hcts, Traced.run]
theorem run_specList (inst : formalism.scheme.Traced P Op Tau) (p : P) (I : Traced Op Tau)
    (hI : TracedSpec inst p I) :
    ∀ (ms : List (Node Op)), FitsList I ms →
      ∀ (j : ℕ) (hj : j < ms.length) (node : formalism.scheme.Node Op), NodeRel node ms[j] →
        formalism.scheme.run inst p node ⦃ (t : alloc.vec.Vec (formalism.scheme.Row Tau)) =>
          tableOf t = Traced.run I ms[j] ⦄
  | [], _, _, hj, _, _ => absurd hj (Nat.not_lt_zero _)
  | m :: _, hfit, 0, _, node, hrel => run_spec inst p I hI m node hrel hfit.1
  | _ :: ms, hfit, j + 1, hj, node, hrel =>
    run_specList inst p I hI ms hfit.2 j (by simpa using hj) node hrel
end

/-! ## `solve`: the accepted root rows -/

omit [DecidableEq Tau] in
theorem solve_loop_spec (inst : formalism.scheme.Traced P Op Tau) (p : P)
    (I : Traced Op Tau) (hI : TracedSpec inst p I)
    (table : alloc.vec.Vec (formalism.scheme.Row Tau)) (e : formalism.expr.Expr) (i : Usize)
    (hi : i.val ≤ table.val.length)
    (he : ofExt e = ((tableOf table).take i.val).foldl
      (fun e row => if I.accept row.1 then Expr.union' e row.2 else e) .empty) :
    formalism.scheme.solve_loop inst p table e i ⦃ (e' : formalism.expr.Expr) =>
      ofExt e' = (tableOf table).foldl
        (fun e row => if I.accept row.1 then Expr.union' e row.2 else e) .empty ⦄ := by
  unfold formalism.scheme.solve_loop
  apply loop.spec_decr_nat (measure := fun s => table.val.length - s.2.val)
    (inv := fun s => s.2.val ≤ table.val.length ∧ ofExt s.1 = ((tableOf table).take s.2.val).foldl
      (fun e row => if I.accept row.1 then Expr.union' e row.2 else e) .empty)
  · rintro ⟨e1, i1⟩ ⟨hi1, he1⟩
    replace hi1 : i1.val ≤ table.val.length := hi1
    replace he1 : ofExt e1 = ((tableOf table).take i1.val).foldl
      (fun e row => if I.accept row.1 then Expr.union' e row.2 else e) .empty := he1
    unfold formalism.scheme.solve_loop.body
    simp only [alloc.vec.Vec.index_slice_index]
    split
    · rename_i hlt
      have hlt' : i1.val < table.val.length := by scalar_tac
      have hlt'' : i1.val < (tableOf table).length := by rw [length_tableOf]; exact hlt'
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec table i1 hlt')
      intro r hr
      replace hr : r = table.val[i1.val] := hr
      apply WP.spec_bind (hI.accept r.tau)
      intro b hb
      replace hb : b = I.accept r.tau := hb
      have hadd := Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac)
      have hrow? : (tableOf table)[i1.val]? = some (r.tau, ofExt r.expr) := by
        rw [tableOf, List.getElem?_map, List.getElem?_eq_getElem hlt', Option.map_some, ← hr]
        rfl
      have hrow : (tableOf table)[i1.val]'hlt'' = (r.tau, ofExt r.expr) :=
        Option.some.inj ((List.getElem?_eq_getElem hlt'').symm.trans hrow?)
      have htake := List.take_succ_eq_append_getElem hlt''
      cases hacc : I.accept r.tau with
      | true =>
        rw [hacc] at hb
        subst hb
        rw [ite_eq_left rfl]
        have hinner : (do
            let e2 ← formalism.expr.Expr.Insts.CoreCloneClone.clone r.expr
            formalism.expr.union e1 e2 : Result formalism.expr.Expr)
            ⦃ (e3 : formalism.expr.Expr) => ofExt e3 = Expr.union' (ofExt e1) (ofExt r.expr) ⦄ := by
          apply WP.spec_bind (clone_spec r.expr)
          intro e2 he2
          replace he2 : e2 = r.expr := he2
          subst he2
          exact union_spec e1 r.expr
        apply WP.spec_bind hinner
        intro e3 he3
        replace he3 : ofExt e3 = Expr.union' (ofExt e1) (ofExt r.expr) := he3
        apply WP.spec_bind hadd
        intro i2 hi2
        replace hi2 : i2.val = i1.val + (1#usize).val := hi2
        have hi2' : i2.val = i1.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
        rw [he3, he1, hi2', htake, List.foldl_append, List.foldl_cons, List.foldl_nil, hrow]
        simp [hacc]
      | false =>
        rw [hacc] at hb
        subst hb
        rw [ite_eq_right Bool.false_ne_true]
        apply WP.spec_bind ((WP.spec_ok (p := fun x => x = e1) _).mpr rfl)
        intro e3 he3
        replace he3 : e3 = e1 := he3
        subst e3
        apply WP.spec_bind hadd
        intro i2 hi2
        replace hi2 : i2.val = i1.val + (1#usize).val := hi2
        have hi2' : i2.val = i1.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
        rw [he1, hi2', htake, List.foldl_append, List.foldl_cons, List.foldl_nil, hrow]
        simp [hacc]
    · rename_i hge
      have htake : (tableOf table).take i1.val = tableOf table :=
        List.take_of_length_le (by rw [length_tableOf]; scalar_tac)
      simp only [WP.spec_ok]
      rw [he1, htake]
  · exact ⟨hi, he⟩

/-- `scheme::solve` computes the model's `solve`. -/
theorem solve_spec (inst : formalism.scheme.Traced P Op Tau) (p : P) (I : Traced Op Tau)
    (hI : TracedSpec inst p I) (m : Node Op) (root : formalism.scheme.Node Op)
    (hrel : NodeRel root m) (hfit : Fits I m) :
    formalism.scheme.solve inst p root ⦃ (e : formalism.expr.Expr) => ofExt e = Traced.solve I m ⦄ := by
  unfold formalism.scheme.solve
  apply WP.spec_bind (run_spec inst p I hI m root hrel hfit)
  intro table htable
  replace htable : tableOf table = Traced.run I m := htable
  apply WP.spec_mono (solve_loop_spec inst p I hI table formalism.expr.Expr.Empty 0#usize
    (by scalar_tac) (by simp [ofExt]))
  intro e he
  rw [he, htable, Traced.solve]

/-! ## Claim 1 about the Rust -/

/-- Claim 1 for the extracted code: on a well-formed construction that the Rust can hold,
    `scheme::solve` succeeds and its expression denotes exactly the solution set. -/
theorem solve_sound_extracted (inst : formalism.scheme.Traced P Op Tau) (p : P)
    (I : Instance Op Tau) (hI : TracedSpec inst p I.toTraced) (m : Node Op)
    (root : formalism.scheme.Node Op) (hrel : NodeRel root m) (hfit : Fits I.toTraced m)
    (hwf : I.WF m) :
    formalism.scheme.solve inst p root ⦃ (e : formalism.expr.Expr) =>
      Sem (ofExt e) ((I.candidates m).filter fun f => I.accept (I.trace m f) = true) ⦄ := by
  apply WP.spec_mono (solve_spec inst p I.toTraced hI m root hrel hfit)
  intro e he
  rw [he]
  exact Formalism.solve_sound I hwf

end Run

end Formalism.Refine
