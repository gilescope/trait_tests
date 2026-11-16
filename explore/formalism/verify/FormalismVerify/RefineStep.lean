import FormalismVerify.Refine
import FormalismVerify.Odometer

/-!
# Refinement of `scheme::step_node`

`step_node` enumerates one row from each child with an odometer (`Odometer.lean` has its pure
side); this file shows the extracted loops compute `Traced.stepNode`, given an extracted
`Traced` implementation that computes the model's `step` and `accept` (`TracedSpec`).
-/

namespace Formalism.Refine
open Aeneas Aeneas.Std Result hylo Odometer

/-! ## List helpers -/

theorem forall₂_getElem {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i]
  | [], [], _, _, h₁, _ => absurd h₁ (Nat.not_lt_zero _)
  | _ :: _, [], h, _, _, _ => nomatch h
  | [], _ :: _, h, _, _, _ => nomatch h
  | _ :: _, _ :: _, h, 0, _, _ => (List.forall₂_cons.mp h).1
  | _ :: _, _ :: _, h, i + 1, h₁, h₂ =>
    forall₂_getElem (List.forall₂_cons.mp h).2 i (by simpa using h₁) (by simpa using h₂)

/-- `incr` leaves a prefix alone when the suffix does not carry. -/
theorem incr_append_of_not_carry :
    ∀ (pm pi ms is : List ℕ), pi.length = pm.length → (incr ms is).2 = false →
      incr (pm ++ ms) (pi ++ is) = (pi ++ (incr ms is).1, false)
  | [], [], ms, is, _, h => by
    rcases hinc : incr ms is with ⟨is', c⟩
    rw [hinc] at h
    simp only at h
    subst h
    simp
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | m :: pm, i :: pi, ms, is, hl, h => by
    have ih := incr_append_of_not_carry pm pi ms is (by simpa using hl) h
    simp only [List.cons_append, incr, ih]
    simp

section Step
variable {P Op Tau : Type} [DecidableEq Tau]

/-- An extracted `Traced` implementation that computes a model instance `I`: `step` and
    `accept` agree, and `Tau`'s clone and equality are honest. -/
structure TracedSpec (inst : formalism.scheme.Traced P Op Tau) (p : P) (I : Traced Op Tau) :
    Prop where
  eq : EqSpec inst.corecmpPartialEqInst
  clone : ∀ a : Tau, inst.corecloneCloneInst.clone a ⦃ (r : Tau) => r = a ⦄
  step : ∀ (op : Op) (s : Slice Tau),
    inst.step p op s ⦃ (outs : alloc.vec.Vec (Tau × alloc.vec.Vec (U32 × U32))) =>
      outs.val.map (fun o => (o.1, ofPairs o.2.val)) = I.step op s.val ⦄
  accept : ∀ t : Tau, inst.accept p t ⦃ (b : Bool) => b = I.accept t ⦄

/-- The children's tables, read back. -/
def tablesOf (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau))) :
    List (List (Tau × Expr)) :=
  cts.val.map tableOf

/-- A digit vector, read back. -/
def idxN (idx : alloc.vec.Vec Usize) : List ℕ := idx.val.map Usize.val

theorem length_tableOf (t : alloc.vec.Vec (formalism.scheme.Row Tau)) :
    (tableOf t).length = t.length := by
  simp [tableOf]

theorem lens_tablesOf (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau))) :
    (tablesOf cts).map List.length = cts.val.map fun t => t.length := by
  simp [tablesOf, length_tableOf]

/-- The model's items at a tuple, in terms of what the extracted `step` returned. -/
theorem rowItems_eq (I : Traced Op Tau) (op : Op) (cur : List (Tau × Expr))
    (outs : alloc.vec.Vec (Tau × alloc.vec.Vec (U32 × U32)))
    (hstep : outs.val.map (fun o => (o.1, ofPairs o.2.val)) = I.step op (cur.map Prod.fst)) :
    Traced.rowItems I op cur =
      outs.val.map fun o => (o.1, Expr.joinLeaves (Traced.joined cur) (ofPairs o.2.val)) := by
  rw [Traced.rowItems, ← hstep, List.map_map]
  rfl

theorem length_le_foldl_rowItems (I : Traced Op Tau) (op : Op) :
    ∀ (rows : List (List (Tau × Expr))) (T : List (Tau × Expr)),
      T.length ≤ (rows.foldl (fun T r =>
        (Traced.rowItems I op r).foldl (fun T it => Traced.unionInto T it.1 it.2) T) T).length
  | [], _ => le_rfl
  | r :: rows, T => by
    rw [List.foldl_cons]
    exact (length_le_foldl_unionInto (Traced.rowItems I op r) T).trans
      (length_le_foldl_rowItems I op rows _)

/-! ## Loop 0: the digit vector starts at zero, and is any child table empty -/

theorem step_node_loop0_spec (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau)))
    (n : Usize) (hn : n.val = cts.length) (idx : alloc.vec.Vec Usize) (any_empty : Bool)
    (k : Usize) (hk : k.val ≤ n.val) (hidx : idxN idx = List.replicate k.val 0)
    (hany : any_empty = true ↔ ∃ j, ∃ (hj : j < k.val), (cts.val[j]'(by scalar_tac)).length = 0) :
    formalism.scheme.step_node_loop0 cts n idx any_empty k
      ⦃ (idx' : alloc.vec.Vec Usize) (any' : Bool) =>
        idxN idx' = List.replicate n.val 0 ∧
        (any' = true ↔ ∃ t ∈ cts.val, t.length = 0) ⦄ := by
  unfold formalism.scheme.step_node_loop0
  apply loop.spec_decr_nat (measure := fun s => n.val - s.2.2.val)
    (inv := fun s => s.2.2.val ≤ n.val ∧ idxN s.1 = List.replicate s.2.2.val 0 ∧
      (s.2.1 = true ↔ ∃ j, ∃ (hj : j < s.2.2.val), (cts.val[j]'(by scalar_tac)).length = 0))
  · rintro ⟨idx1, any1, k1⟩ ⟨hk1, hidx1, hany1⟩
    replace hk1 : k1.val ≤ n.val := hk1
    replace hidx1 : idxN idx1 = List.replicate k1.val 0 := hidx1
    replace hany1 : any1 = true ↔ ∃ j, ∃ (hj : j < k1.val), (cts.val[j]'(by scalar_tac)).length = 0 :=
      hany1
    beta_reduce
    unfold formalism.scheme.step_node_loop0.body
    simp only [alloc.vec.Vec.index_slice_index]
    split
    · rename_i hlt
      have hlt' : k1.val < cts.length := by scalar_tac
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec cts k1 hlt')
      intro v hv
      replace hv : v = cts.val[k1.val] := hv
      simp only [alloc.vec.Vec.is_empty, bind_tc_ok]
      have hidxlen : idx1.length < Usize.max := by
        have : (idxN idx1).length = k1.val := by rw [hidx1, List.length_replicate]
        simp only [idxN, List.length_map] at this
        scalar_tac
      have hpush := alloc.vec.Vec.push_spec idx1 0#usize hidxlen
      have hadd := Usize.add_spec (x := k1) (y := 1#usize) (by scalar_tac)
      split
      · rename_i hb
        apply WP.spec_bind hpush
        intro idx2 hidx2
        replace hidx2 : idx2.val = idx1.val ++ [0#usize] := hidx2
        apply WP.spec_bind hadd
        intro k2 hk2
        replace hk2 : k2.val = k1.val + (1#usize).val := hk2
        have hk2' : k2.val = k1.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
        · rw [idxN, hidx2, List.map_append, hk2', List.replicate_succ']
          simp only [idxN] at hidx1
          rw [hidx1]
          simp
        · simp only [true_iff]
          refine ⟨k1.val, by rw [hk2']; exact Nat.lt_succ_self _, ?_⟩
          rw [← hv]
          simpa using hb
      · rename_i hb
        apply WP.spec_bind hpush
        intro idx2 hidx2
        replace hidx2 : idx2.val = idx1.val ++ [0#usize] := hidx2
        apply WP.spec_bind hadd
        intro k2 hk2
        replace hk2 : k2.val = k1.val + (1#usize).val := hk2
        have hk2' : k2.val = k1.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
        · rw [idxN, hidx2, List.map_append, hk2', List.replicate_succ']
          simp only [idxN] at hidx1
          rw [hidx1]
          simp
        · rw [hany1]
          constructor
          · rintro ⟨j, hj, hj0⟩
            exact ⟨j, by rw [hk2']; exact Nat.lt_succ_of_lt hj, hj0⟩
          · rintro ⟨j, hj, hj0⟩
            rw [hk2'] at hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
            · exact ⟨j, hj, hj0⟩
            · exfalso
              rw [← hv] at hj0
              simp at hb
              exact hb hj0
    · rename_i hge
      have hkn : k1.val = n.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨by rw [hidx1, hkn], ?_⟩
      rw [hany1]
      constructor
      · rintro ⟨j, hj, hj0⟩
        exact ⟨_, List.getElem_mem _, hj0⟩
      · rintro ⟨t, ht, ht0⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
        exact ⟨j, by rw [hkn]; exact hn ▸ hj, ht0⟩
  · exact ⟨hk, hidx, hany⟩

/-! ## Loop 1.0: the traces and the join of the current tuple of rows -/

/-- The current tuple of rows, as the odometer lemma describes it: at each child, the row the
    digit addresses. -/
def CurOf (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau)))
    (idx : alloc.vec.Vec Usize) (cur : List (Tau × Expr)) : Prop :=
  List.Forall₂ (fun (r : Tau × Expr) (p : List (Tau × Expr) × ℕ) => p.1[p.2]? = some r) cur
    ((tablesOf cts).zip (idxN idx))

theorem CurOf.length {cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau))}
    {idx : alloc.vec.Vec Usize} {cur : List (Tau × Expr)} (h : CurOf cts idx cur)
    (hlen : idx.length = cts.length) : cur.length = cts.length := by
  have := List.Forall₂.length_eq h
  rw [List.length_zip, tablesOf, idxN, List.length_map, List.length_map] at this
  rw [this, hlen, Nat.min_self]
  rfl

theorem CurOf.getElem {cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau))}
    {idx : alloc.vec.Vec Usize} {cur : List (Tau × Expr)} (h : CurOf cts idx cur)
    (hlen : idx.length = cts.length) (k : ℕ) (hk : k < cts.length) :
    ∃ (hi : (idx.val[k]'(by rw [hlen]; exact hk)).val < (cts.val[k]).length),
      cur[k]'(by rw [h.length hlen]; exact hk) =
        rowOf ((cts.val[k]).val[(idx.val[k]'(by rw [hlen]; exact hk)).val]'hi) := by
  have hz : k < ((tablesOf cts).zip (idxN idx)).length := by
    rw [List.length_zip, tablesOf, idxN, List.length_map, List.length_map, hlen, Nat.min_self]
    exact hk
  have hr := forall₂_getElem h k (by rw [h.length hlen]; exact hk) hz
  simp only [List.getElem_zip, tablesOf, idxN, List.getElem_map, tableOf] at hr
  rw [List.getElem?_map] at hr
  rcases hget : (cts.val[k]).val[(idx.val[k]'(by rw [hlen]; exact hk)).val]? with _ | row
  · rw [hget] at hr
    simp at hr
  · rw [hget] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    have hi := List.getElem?_eq_some_iff.mp hget
    obtain ⟨hi, hrow⟩ := hi
    exact ⟨hi, by rw [hr, hrow]⟩

theorem step_node_loop1_loop0_spec (inst : formalism.scheme.Traced P Op Tau) (p : P)
    (I : Traced Op Tau) (hI : TracedSpec inst p I)
    (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau))) (n : Usize)
    (hn : n.val = cts.length) (idx : alloc.vec.Vec Usize) (hlen : idx.length = cts.length)
    (cur : List (Tau × Expr)) (hcur : CurOf cts idx cur)
    (traces : alloc.vec.Vec Tau) (joined : formalism.expr.Expr) (k : Usize) (hk : k.val ≤ n.val)
    (htr : traces.val = (cur.take k.val).map Prod.fst)
    (hj : ofExt joined = (cur.take k.val).foldl (fun acc r => Expr.join' acc r.2) .unit) :
    formalism.scheme.step_node_loop1_loop0 inst cts n idx traces joined k
      ⦃ (traces' : alloc.vec.Vec Tau) (joined' : formalism.expr.Expr) =>
        traces'.val = cur.map Prod.fst ∧ ofExt joined' = Traced.joined cur ⦄ := by
  unfold formalism.scheme.step_node_loop1_loop0
  apply loop.spec_decr_nat (measure := fun s => n.val - s.2.2.val)
    (inv := fun s => s.2.2.val ≤ n.val ∧ s.1.val = (cur.take s.2.2.val).map Prod.fst ∧
      ofExt s.2.1 = (cur.take s.2.2.val).foldl (fun acc r => Expr.join' acc r.2) .unit)
  · rintro ⟨traces1, joined1, k1⟩ ⟨hk1, htr1, hj1⟩
    replace hk1 : k1.val ≤ n.val := hk1
    replace htr1 : traces1.val = (cur.take k1.val).map Prod.fst := htr1
    replace hj1 : ofExt joined1 = (cur.take k1.val).foldl (fun acc r => Expr.join' acc r.2) .unit :=
      hj1
    beta_reduce
    unfold formalism.scheme.step_node_loop1_loop0.body
    simp only [alloc.vec.Vec.index_slice_index]
    split
    · rename_i hlt
      have hlt' : k1.val < cts.length := by scalar_tac
      have hlt'' : k1.val < idx.length := by rw [hlen]; exact hlt'
      obtain ⟨hi, hcurk⟩ := hcur.getElem hlen k1.val hlt'
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec cts k1 hlt')
      intro v hv
      replace hv : v = cts.val[k1.val] := hv
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec idx k1 hlt'')
      intro i hi'
      replace hi' : i = idx.val[k1.val] := hi'
      have hiv : i.val < v.length := by rw [hv, hi']; exact hi
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec v i hiv)
      intro row hrow
      replace hrow : row = v.val[i.val] := hrow
      apply WP.spec_bind (hI.clone row.tau)
      intro t ht
      replace ht : t = row.tau := ht
      subst ht
      have htrlen : traces1.length < Usize.max := by
        have : traces1.val.length ≤ cur.length := by
          rw [htr1, List.length_map]
          exact List.length_take_le _ _
        rw [hcur.length hlen] at this
        scalar_tac
      apply WP.spec_bind (alloc.vec.Vec.push_spec traces1 row.tau htrlen)
      intro traces2 htr2
      replace htr2 : traces2.val = traces1.val ++ [row.tau] := htr2
      apply WP.spec_bind (clone_spec row.expr)
      intro e he
      replace he : e = row.expr := he
      subst he
      apply WP.spec_bind (join_spec joined1 row.expr)
      intro joined2 hj2
      replace hj2 : ofExt joined2 = Expr.join' (ofExt joined1) (ofExt row.expr) := hj2
      apply WP.spec_bind (Usize.add_spec (x := k1) (y := 1#usize) (by scalar_tac))
      intro k2 hk2
      replace hk2 : k2.val = k1.val + (1#usize).val := hk2
      have hk2' : k2.val = k1.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      have hrowk : cur[k1.val]'(by rw [hcur.length hlen]; exact hlt') = rowOf row := by
        rw [hcurk, hrow, hv, hi']
      have htake : cur.take (k1.val + 1) = cur.take k1.val ++ [cur[k1.val]'(by rw [hcur.length hlen]; exact hlt')] :=
        List.take_succ_eq_append_getElem (by rw [hcur.length hlen]; exact hlt')
      refine ⟨⟨by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
      · rw [htr2, htr1, hk2', htake, List.map_append, hrowk]
        rfl
      · rw [hj2, hj1, hk2', htake, List.foldl_append, List.foldl_cons, List.foldl_nil, hrowk]
        rfl
    · rename_i hge
      have hkn : k1.val = n.val := by scalar_tac
      have htake : cur.take k1.val = cur := List.take_of_length_le (by rw [hcur.length hlen, ← hn, hkn])
      simp only [WP.spec_ok]
      rw [htr1, hj1, htake]
      exact ⟨rfl, rfl⟩
  · exact ⟨hk, htr, hj⟩

/-! ## Loop 1.1: every output of `step` goes into the table -/

theorem step_node_loop1_loop1_spec (inst : formalism.scheme.Traced P Op Tau) (p : P)
    (I : Traced Op Tau) (hI : TracedSpec inst p I)
    (table : alloc.vec.Vec (formalism.scheme.Row Tau)) (joined : formalism.expr.Expr)
    (J : Expr) (hJ : ofExt joined = J)
    (outs : alloc.vec.Vec (Tau × alloc.vec.Vec (U32 × U32))) (T0 : List (Tau × Expr))
    (hfin : ((outs.val.map fun o => (o.1, Expr.joinLeaves J (ofPairs o.2.val))).foldl
      (fun T it => Traced.unionInto T it.1 it.2) T0).length < Usize.max)
    (o : Usize) (ho : o.val ≤ outs.length)
    (htab : tableOf table =
      ((outs.val.map fun o => (o.1, Expr.joinLeaves J (ofPairs o.2.val))).take o.val).foldl
        (fun T it => Traced.unionInto T it.1 it.2) T0) :
    formalism.scheme.step_node_loop1_loop1 inst table joined outs o
      ⦃ (table' : alloc.vec.Vec (formalism.scheme.Row Tau)) =>
        tableOf table' = (outs.val.map fun o => (o.1, Expr.joinLeaves J (ofPairs o.2.val))).foldl
          (fun T it => Traced.unionInto T it.1 it.2) T0 ⦄ := by
  unfold formalism.scheme.step_node_loop1_loop1
  apply loop.spec_decr_nat (measure := fun s => outs.length - s.2.val)
    (inv := fun s => s.2.val ≤ outs.length ∧ tableOf s.1 =
      ((outs.val.map fun o => (o.1, Expr.joinLeaves J (ofPairs o.2.val))).take s.2.val).foldl
        (fun T it => Traced.unionInto T it.1 it.2) T0)
  · rintro ⟨table1, o1⟩ ⟨ho1, htab1⟩
    replace ho1 : o1.val ≤ outs.length := ho1
    replace htab1 : tableOf table1 =
      ((outs.val.map fun o => (o.1, Expr.joinLeaves J (ofPairs o.2.val))).take o1.val).foldl
        (fun T it => Traced.unionInto T it.1 it.2) T0 := htab1
    beta_reduce
    unfold formalism.scheme.step_node_loop1_loop1.body
    simp only [alloc.vec.Vec.index_slice_index]
    split
    · rename_i hlt
      have hlt' : o1.val < outs.length := by scalar_tac
      have hlt'' : o1.val < (outs.val.map fun o => (o.1, Expr.joinLeaves J (ofPairs o.2.val))).length := by
        rw [List.length_map]
        exact hlt'
      apply WP.spec_bind (clone_spec joined)
      intro e he
      replace he : e = joined := he
      subst he
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec outs o1 hlt')
      rintro ⟨t, v⟩ htv
      replace htv : (t, v) = outs.val[o1.val] := htv
      dsimp only
      apply WP.spec_bind (join_leaves_spec joined (alloc.vec.Vec.deref v))
      intro e1 he1
      replace he1 : ofExt e1 =
        Expr.joinLeaves (ofExt joined) (ofPairs (alloc.vec.Vec.deref v).val) := he1
      have hvv : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
      rw [hJ, hvv] at he1
      apply WP.spec_bind (hI.clone t)
      intro t1 ht1
      replace ht1 : t1 = t := ht1
      subst ht1
      have hlen1 : table1.length < Usize.max := by
        rw [← length_tableOf, htab1]
        refine lt_of_le_of_lt ?_ hfin
        conv_rhs => rw [← List.take_append_drop o1.val
          (outs.val.map fun o => (o.1, Expr.joinLeaves J (ofPairs o.2.val))), List.foldl_append]
        exact length_le_foldl_unionInto _ _
      apply WP.spec_bind (union_into_spec inst.corecmpPartialEqInst hI.eq table1 t e1 hlen1)
      intro table2 htab2
      replace htab2 : tableOf table2 = Traced.unionInto (tableOf table1) t (ofExt e1) := htab2
      apply WP.spec_bind (Usize.add_spec (x := o1) (y := 1#usize) (by scalar_tac))
      intro o2 ho2
      replace ho2 : o2.val = o1.val + (1#usize).val := ho2
      have ho2' : o2.val = o1.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      rw [htab2, htab1, he1, ho2', List.take_succ_eq_append_getElem hlt'', List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.getElem_map, ← htv]
    · rename_i hge
      have htake : (outs.val.map fun o => (o.1, Expr.joinLeaves J (ofPairs o.2.val))).take o1.val =
          outs.val.map fun o => (o.1, Expr.joinLeaves J (ofPairs o.2.val)) :=
        List.take_of_length_le (by rw [List.length_map]; scalar_tac)
      simp only [WP.spec_ok]
      rw [htab1, htake]
  · exact ⟨ho, htab⟩

end Step

end Formalism.Refine
