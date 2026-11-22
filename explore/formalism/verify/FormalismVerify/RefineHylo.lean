import FormalismVerify.RefineRun

/-!
# `hylo::dp::trace_dp` computes the model's `solve`

`trace_dp` is the trace DP written as a rose hylomorphism: `hylo_rose` pops the children off the
back, runs each, reverses the results back into order and folds the layer with `step_node`;
`trace_dp` then reverses the root table and pops its rows, taking the accepted ones into a
union. Read through a representation `R`, it computes `Traced.solve` too (`trace_dp_spec`), so
Claim 1 holds of it as of `scheme::solve` (`trace_dp_sound_extracted`).
-/

namespace Formalism.Refine
open Aeneas Aeneas.Std Result hylo

section Hylo
variable {P Op' Tau' Op Tau : Type} [DecidableEq Tau] (R : Repr Op' Tau' Op Tau)

/-- The last element of a vector read through `tableOf`. -/
theorem tablesOf_append (v : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau')))
    (w : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau')))
    (t : alloc.vec.Vec (formalism.scheme.Row Tau')) (h : w.val = v.val ++ [t]) :
    tablesOf R w = tablesOf R v ++ [tableOf R t] := by
  rw [tablesOf, h, List.map_append, List.map_singleton]
  rfl

/-- The pop loop of `hylo_rose`: the children run from the last to the first, their tables
    pushed in that order. -/
theorem hylo_rose_loop_spec (inst : formalism.scheme.Traced P Op' Tau') (p : P)
    (I : Traced Op Tau) (ks : List (formalism.scheme.Node Op')) (ms : List (Node Op))
    (hrel : NodeRelList R ks ms) (hks : ks.length ≤ Usize.max)
    (hIH : ∀ (j : ℕ) (hj : j < ms.length) (n' : formalism.scheme.Node Op') (plan : Unit),
      NodeRel R n' ms[j] →
      hylo.shape.hylo_rose (hylo.dp.Project.Insts.HyloShapeRosePlanOpNode Op')
        (hylo.dp.TraceDp.Insts.HyloShapeRoseAlgebraClause0_OpVecRow inst) plan p n'
        ⦃ (r : alloc.vec.Vec (formalism.scheme.Row Tau') × Unit × P) =>
          tableOf R r.1 = Traced.run I ms[j] ∧ r.2.2 = p ⦄)
    (kids : alloc.vec.Vec (formalism.scheme.Node Op')) (plan : Unit)
    (out : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau')))
    (j : ℕ) (hj : j ≤ ks.length) (hkids : kids.val = ks.take j)
    (hout : tablesOf R out = (Traced.runList I (ms.drop j)).reverse) :
    hylo.shape.hylo_rose_loop (hylo.dp.Project.Insts.HyloShapeRosePlanOpNode Op')
      (hylo.dp.TraceDp.Insts.HyloShapeRoseAlgebraClause0_OpVecRow inst) kids plan p out
      ⦃ (r : Unit × P × alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau'))) =>
        r.2.1 = p ∧ tablesOf R r.2.2 = (Traced.runList I ms).reverse ⦄ := by
  have hlen : ks.length = ms.length := NodeRelList.length_eq R hrel
  unfold hylo.shape.hylo_rose_loop
  apply loop.spec_decr_nat (measure := fun s => s.1.val.length)
    (inv := fun s => s.2.2.1 = p ∧ ∃ j ≤ ks.length, s.1.val = ks.take j ∧
      tablesOf R s.2.2.2 = (Traced.runList I (ms.drop j)).reverse)
  · rintro ⟨kids1, plan1, alg1, out1⟩ ⟨halg, j1, hj1, hkids1, hout1⟩
    replace halg : alg1 = p := halg
    replace hkids1 : kids1.val = ks.take j1 := hkids1
    replace hout1 : tablesOf R out1 = (Traced.runList I (ms.drop j1)).reverse := hout1
    subst alg1
    show hylo.shape.hylo_rose_loop.body _ _ kids1 plan1 p out1 ⦃ _ ⦄
    unfold hylo.shape.hylo_rose_loop.body
    apply WP.spec_bind (alloc.vec.Vec.pop_spec kids1)
    rintro ⟨o, kids2⟩ hpop
    have hpop' : o = kids1.val.getLast? ∧ kids2.val = kids1.val.dropLast := hpop
    obtain ⟨ho, hkids2⟩ := hpop'
    cases j1 with
    | zero =>
      rw [hkids1, List.take_zero, List.getLast?_nil] at ho
      subst ho
      show WP.spec (ok (ControlFlow.done (plan1, p, out1))) _
      rw [WP.spec_ok]
      refine ⟨by trivial, ?_⟩
      show tablesOf R out1 = _
      rw [hout1, List.drop_zero]
    | succ j' =>
      have hj' : j' < ks.length := hj1
      have hj'' : j' < ms.length := by rw [← hlen]; exact hj'
      rw [List.take_succ_eq_append_getElem hj'] at hkids1
      rw [hkids1, List.getLast?_concat] at ho
      rw [hkids1, List.dropLast_concat] at hkids2
      subst ho
      try dsimp only
      apply WP.spec_bind (hIH j' hj'' ks[j'] plan1 (NodeRelList.getElem R hrel j' hj' hj''))
      rintro ⟨t, plan2, alg2⟩ hr
      have hr' : tableOf R t = Traced.run I ms[j'] ∧ alg2 = p := hr
      obtain ⟨ht, halg2⟩ := hr'
      subst alg2
      have hlen1 : out1.val.length < Usize.max := by
        have h1 := length_tablesOf R out1
        rw [hout1, List.length_reverse, runList_length, List.length_drop] at h1
        omega
      apply WP.spec_bind (alloc.vec.Vec.push_spec out1 t hlen1)
      intro out2 hout2
      replace hout2 : out2.val = out1.val ++ [t] := hout2
      simp only [WP.spec_ok]
      refine ⟨⟨by trivial, j', hj'.le, hkids2, ?_⟩, ?_⟩
      · rw [tablesOf_append R out1 out2 t hout2, hout1, ht, List.drop_eq_getElem_cons hj'',
          Traced.runList, List.reverse_cons]
      · rw [hkids2, hkids1, List.length_append, List.length_singleton]
        omega
  · exact ⟨by trivial, j, hj, hkids, hout⟩

-- `hylo_rose` computes `run`; the one way it fails is a table that does not fit (`Fits`).
mutual
theorem hylo_rose_spec (inst : formalism.scheme.Traced P Op' Tau') (p : P) (I : Traced Op Tau)
    {okP : Op → List Tau → Prop} (hI : TracedSpec R inst p I okP) :
    ∀ (m : Node Op) (node : formalism.scheme.Node Op') (plan : Unit), NodeRel R node m →
      Fits I m → StepsOk I okP m →
      hylo.shape.hylo_rose (hylo.dp.Project.Insts.HyloShapeRosePlanOpNode Op')
        (hylo.dp.TraceDp.Insts.HyloShapeRoseAlgebraClause0_OpVecRow inst) plan p node
        ⦃ (r : alloc.vec.Vec (formalism.scheme.Row Tau') × Unit × P) =>
          tableOf R r.1 = Traced.run I m ∧ r.2.2 = p ⦄
  | .mk op ms, .mk nop ncs, plan, hrel, hfit, hok => by
    rw [Fits] at hfit
    obtain ⟨hfin, hfits⟩ := hfit
    rw [StepsOk] at hok
    obtain ⟨hok1, hoks⟩ := hok
    have hrel' := hrel
    rw [NodeRel] at hrel'
    obtain ⟨hop, hrelL⟩ := hrel'
    have hlen : ncs.val.length = ms.length := NodeRelList.length_eq R hrelL
    unfold hylo.shape.hylo_rose
    simp only [hylo.dp.Project.Insts.HyloShapeRosePlanOpNode,
      hylo.dp.Project.Insts.HyloShapeRosePlanOpNode.unfold,
      formalism.scheme.Node.op._simpLemma_, formalism.scheme.Node.children._simpLemma_]
    apply WP.spec_bind ((WP.spec_ok (p := fun r => r = ((nop, ncs), plan)) _).mpr rfl)
    rintro ⟨⟨t, kids⟩, plan1⟩ hu
    have hu' : ((t, kids), plan1) = ((nop, ncs), plan) := hu
    simp only [Prod.mk.injEq] at hu'
    obtain ⟨⟨ht, hkids⟩, hplan1⟩ := hu'
    subst t kids
    try dsimp only
    apply WP.spec_bind (hylo_rose_loop_spec R inst p I ncs.val ms hrelL ncs.property
      (fun j hj n' plan' hrel' => hylo_rose_specList inst p I hI ms hfits hoks j hj n' plan' hrel')
      ncs plan1 (alloc.vec.Vec.new _) ncs.val.length le_rfl List.take_length.symm
      (by simp [tablesOf, alloc.vec.Vec.new, hlen, Traced.runList]))
    rintro ⟨plan2, alg1, out⟩ hr
    have hr' : alg1 = p ∧ tablesOf R out = (Traced.runList I ms).reverse := hr
    obtain ⟨halg1, hout⟩ := hr'
    subst alg1
    have hrev : ∀ v : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau')),
        v.val = out.val.reverse → tablesOf R v = Traced.runList I ms := by
      intro v hv
      rw [tablesOf, hv, List.map_reverse]
      show (tablesOf R out).reverse = _
      rw [hout, List.reverse_reverse]
    apply WP.spec_bind ((WP.spec_ok (p := fun r => r = alloc.vec.Vec.deref_mut out) _).mpr rfl)
    rintro ⟨s, back⟩ hsb
    have hsb' : (s, back) = alloc.vec.Vec.deref_mut out := hsb
    rw [alloc.vec.Vec.deref_mut, Prod.mk.injEq] at hsb'
    obtain ⟨hs, hback⟩ := hsb'
    subst hs hback
    apply WP.spec_bind
      ((WP.spec_ok (p := fun r => r = core.slice.Slice.reverse out.slice) _).mpr rfl)
    intro s1 hs1
    subst hs1
    try dsimp only
    have hout1 : tablesOf R { slice := core.slice.Slice.reverse out.slice } =
        Traced.runList I ms := by
      apply hrev
      show (core.slice.Slice.reverse out.slice).val = out.val.reverse
      rw [core.slice.Slice.reverse, Slice.from_val]
      rfl
    simp only [hylo.dp.TraceDp.Insts.HyloShapeRoseAlgebraClause0_OpVecRow,
      hylo.dp.TraceDp.Insts.HyloShapeRoseAlgebraClause0_OpVecRow.fold]
    have hinner : (do
        let v ← formalism.scheme.step_node inst p nop { slice := core.slice.Slice.reverse out.slice }
        ok (v, p) : Result (alloc.vec.Vec (formalism.scheme.Row Tau') × P))
        ⦃ (r : alloc.vec.Vec (formalism.scheme.Row Tau') × P) =>
          tableOf R r.1 = Traced.run I (.mk op ms) ∧ r.2 = p ⦄ := by
      apply WP.spec_bind (step_node_spec R inst p I hI nop _ (by rw [hout1, hop]; exact hfin)
        (by rw [hout1, hop]; exact hok1))
      intro v hv
      replace hv : tableOf R v = Traced.stepNode I (R.opOf nop)
        (tablesOf R { slice := core.slice.Slice.reverse out.slice }) := hv
      simp only [WP.spec_ok]
      exact ⟨by rw [hv, hout1, hop, Traced.run], by trivial⟩
    apply WP.spec_bind hinner
    rintro ⟨t1, alg2⟩ hr1
    have hr1' : tableOf R t1 = Traced.run I (.mk op ms) ∧ alg2 = p := hr1
    obtain ⟨ht1, halg2⟩ := hr1'
    subst alg2
    show WP.spec (ok (t1, plan2, p)) _
    rw [WP.spec_ok]
    exact ⟨ht1, by trivial⟩
theorem hylo_rose_specList (inst : formalism.scheme.Traced P Op' Tau') (p : P)
    (I : Traced Op Tau) {okP : Op → List Tau → Prop} (hI : TracedSpec R inst p I okP) :
    ∀ (ms : List (Node Op)), FitsList I ms → StepsOkList I okP ms →
      ∀ (j : ℕ) (hj : j < ms.length) (node : formalism.scheme.Node Op') (plan : Unit),
        NodeRel R node ms[j] →
        hylo.shape.hylo_rose (hylo.dp.Project.Insts.HyloShapeRosePlanOpNode Op')
          (hylo.dp.TraceDp.Insts.HyloShapeRoseAlgebraClause0_OpVecRow inst) plan p node
          ⦃ (r : alloc.vec.Vec (formalism.scheme.Row Tau') × Unit × P) =>
            tableOf R r.1 = Traced.run I ms[j] ∧ r.2.2 = p ⦄
  | [], _, _, _, hj, _, _, _ => absurd hj (Nat.not_lt_zero _)
  | m :: _, hfit, hok, 0, _, node, plan, hrel =>
    hylo_rose_spec inst p I hI m node plan hrel hfit.1 hok.1
  | _ :: ms, hfit, hok, j + 1, hj, node, plan, hrel =>
    hylo_rose_specList inst p I hI ms hfit.2 hok.2 j (by simpa using hj) node plan hrel
end

/-- The pop loop of `trace_dp`: the rows of the reversed table, popped from the back, are the
    table's rows in order. -/
theorem trace_dp_loop_spec (inst : formalism.scheme.Traced P Op' Tau') (p : P)
    (I : Traced Op Tau) {okP : Op → List Tau → Prop} (hI : TracedSpec R inst p I okP)
    (T : List (formalism.scheme.Row Tau'))
    (table : alloc.vec.Vec (formalism.scheme.Row Tau')) (e : formalism.expr.Expr)
    (j : ℕ) (hj : j ≤ T.length) (htable : table.val = (T.drop j).reverse)
    (he : ofExt e = ((T.map (rowOf R)).take j).foldl
      (fun e row => if I.accept row.1 then Expr.union' e row.2 else e) .empty) :
    hylo.dp.trace_dp_loop inst table p e ⦃ (e' : formalism.expr.Expr) =>
      ofExt e' = (T.map (rowOf R)).foldl
        (fun e row => if I.accept row.1 then Expr.union' e row.2 else e) .empty ⦄ := by
  unfold hylo.dp.trace_dp_loop
  apply loop.spec_decr_nat (measure := fun s => s.1.val.length)
    (inv := fun s => ∃ j ≤ T.length, s.1.val = (T.drop j).reverse ∧
      ofExt s.2 = ((T.map (rowOf R)).take j).foldl
        (fun e row => if I.accept row.1 then Expr.union' e row.2 else e) .empty)
  · rintro ⟨table1, e1⟩ ⟨j1, hj1, htable1, he1⟩
    replace htable1 : table1.val = (T.drop j1).reverse := htable1
    replace he1 : ofExt e1 = ((T.map (rowOf R)).take j1).foldl
      (fun e row => if I.accept row.1 then Expr.union' e row.2 else e) .empty := he1
    show hylo.dp.trace_dp_loop.body inst p table1 e1 ⦃ _ ⦄
    unfold hylo.dp.trace_dp_loop.body
    apply WP.spec_bind (alloc.vec.Vec.pop_spec table1)
    rintro ⟨o, table2⟩ hpop
    have hpop' : o = table1.val.getLast? ∧ table2.val = table1.val.dropLast := hpop
    obtain ⟨ho, htable2⟩ := hpop'
    rcases Nat.lt_or_ge j1 T.length with hlt | hge
    · have hlt' : j1 < (T.map (rowOf R)).length := by rw [List.length_map]; exact hlt
      rw [List.drop_eq_getElem_cons hlt, List.reverse_cons] at htable1
      rw [htable1, List.getLast?_concat] at ho
      rw [htable1, List.dropLast_concat] at htable2
      subst ho
      try dsimp only
      apply WP.spec_bind (hI.accept T[j1].tau)
      intro b hb
      replace hb : b = I.accept (R.tauOf T[j1].tau) := hb
      have hrow : (T.map (rowOf R))[j1]'hlt' = (R.tauOf T[j1].tau, ofExt T[j1].expr) := by
        rw [List.getElem_map]
        rfl
      have htake := List.take_succ_eq_append_getElem hlt'
      have hmeasure : table2.val.length < table1.val.length := by
        rw [htable2, htable1, List.length_append, List.length_singleton]
        omega
      cases hacc : I.accept (R.tauOf T[j1].tau) with
      | true =>
        rw [hacc] at hb
        subst hb
        rw [ite_eq_left rfl]
        apply WP.spec_bind (union_spec e1 T[j1].expr)
        intro e2 he2
        replace he2 : ofExt e2 = Expr.union' (ofExt e1) (ofExt T[j1].expr) := he2
        simp only [WP.spec_ok]
        refine ⟨⟨j1 + 1, hlt, htable2, ?_⟩, hmeasure⟩
        rw [he2, he1, htake, List.foldl_append, List.foldl_cons, List.foldl_nil, hrow]
        simp [hacc]
      | false =>
        rw [hacc] at hb
        subst hb
        rw [ite_eq_right Bool.false_ne_true]
        simp only [WP.spec_ok]
        refine ⟨⟨j1 + 1, hlt, htable2, ?_⟩, hmeasure⟩
        rw [he1, htake, List.foldl_append, List.foldl_cons, List.foldl_nil, hrow]
        simp [hacc]
    · have hj1' : j1 = T.length := le_antisymm hj1 hge
      rw [hj1', List.drop_length, List.reverse_nil] at htable1
      rw [htable1, List.getLast?_nil] at ho
      subst ho
      show WP.spec (ok (ControlFlow.done e1)) _
      rw [WP.spec_ok]
      show ofExt e1 = _
      rw [he1, hj1', List.take_of_length_le (by rw [List.length_map])]
  · exact ⟨j, hj, htable, he⟩

/-- `trace_dp` computes the model's `solve`. -/
theorem trace_dp_spec (inst : formalism.scheme.Traced P Op' Tau') (p : P) (I : Traced Op Tau)
    {okP : Op → List Tau → Prop} (hI : TracedSpec R inst p I okP) (m : Node Op)
    (root : formalism.scheme.Node Op') (hrel : NodeRel R root m) (hfit : Fits I m)
    (hok : StepsOk I okP m) :
    hylo.dp.trace_dp inst p root ⦃ (e : formalism.expr.Expr) => ofExt e = Traced.solve I m ⦄ := by
  unfold hylo.dp.trace_dp
  apply WP.spec_bind (hylo_rose_spec R inst p I hI m root () hrel hfit hok)
  rintro ⟨table, plan, alg⟩ hr
  have hr' : tableOf R table = Traced.run I m ∧ alg = p := hr
  obtain ⟨htable, _⟩ := hr'
  try dsimp only
  apply WP.spec_bind ((WP.spec_ok (p := fun r => r = alloc.vec.Vec.deref_mut table) _).mpr rfl)
  rintro ⟨s, back⟩ hsb
  have hsb' : (s, back) = alloc.vec.Vec.deref_mut table := hsb
  rw [alloc.vec.Vec.deref_mut, Prod.mk.injEq] at hsb'
  obtain ⟨hs, hback⟩ := hsb'
  subst hs hback
  apply WP.spec_bind
    ((WP.spec_ok (p := fun r => r = core.slice.Slice.reverse table.slice) _).mpr rfl)
  intro s1 hs1
  subst hs1
  try dsimp only
  have hrev : ({ slice := core.slice.Slice.reverse table.slice } :
      alloc.vec.Vec (formalism.scheme.Row Tau')).val = (table.val.drop 0).reverse := by
    show (core.slice.Slice.reverse table.slice).val = _
    rw [core.slice.Slice.reverse, Slice.from_val, List.drop_zero]
    rfl
  apply WP.spec_mono (trace_dp_loop_spec R inst p I hI table.val _ formalism.expr.Expr.Empty 0
    (Nat.zero_le _) hrev (by simp [ofExt]))
  intro e he
  rw [he, Traced.solve, ← htable]
  rfl

/-- Claim 1 for the extracted `hylo::dp::trace_dp`, as `solve_sound_extracted` for
    `scheme::solve`. -/
theorem trace_dp_sound_extracted (inst : formalism.scheme.Traced P Op' Tau') (p : P)
    (I : Instance Op Tau) {okP : Op → List Tau → Prop} (hI : TracedSpec R inst p I.toTraced okP)
    (m : Node Op) (root : formalism.scheme.Node Op') (hrel : NodeRel R root m)
    (hfit : Fits I.toTraced m) (hok : StepsOk I.toTraced okP m) (hwf : I.WF m) :
    hylo.dp.trace_dp inst p root ⦃ (e : formalism.expr.Expr) =>
      Sem (ofExt e) ((I.candidates m).filter fun f => I.accept (I.trace m f) = true) ⦄ := by
  apply WP.spec_mono (trace_dp_spec R inst p I.toTraced hI m root hrel hfit hok)
  intro e he
  rw [he]
  exact Formalism.solve_sound I hwf

end Hylo

end Formalism.Refine
