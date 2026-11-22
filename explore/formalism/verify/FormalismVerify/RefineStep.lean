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
open Traced (tuples)

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
    simp only [List.nil_append]
    exact Prod.ext rfl h
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | m :: pm, i :: pi, ms, is, hl, h => by
    have ih := incr_append_of_not_carry pm pi ms is (by simpa using hl) h
    simp only [List.cons_append, incr, ih]
    simp

theorem map_drop' {α β : Type*} (f : α → β) :
    ∀ (l : List α) (n : ℕ), (l.map f).drop n = (l.drop n).map f
  | [], _ => by simp
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => by
    rw [List.map_cons, List.drop_succ_cons, List.drop_succ_cons, map_drop' f l n]

theorem getElem?_take_of_lt' {α : Type*} :
    ∀ (l : List α) (n m : ℕ), m < n → (l.take n)[m]? = l[m]?
  | [], _, _, _ => by simp
  | _ :: _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ + 1, 0, _ => by simp
  | _ :: l, n + 1, m + 1, h => by
    rw [List.take_succ_cons, List.getElem?_cons_succ, List.getElem?_cons_succ,
      getElem?_take_of_lt' l n m (by omega)]

theorem set_take_append {α : Type*} :
    ∀ (l : List α) (k : ℕ), k < l.length → ∀ (rest : List α) (x : α),
      (l.take (k + 1) ++ rest).set k x = l.take k ++ x :: rest
  | [], _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: _, 0, _, _, _ => by simp
  | a :: l, k + 1, hk, rest, x => by
    rw [List.take_succ_cons, List.take_succ_cons, List.cons_append, List.set_cons_succ,
      List.cons_append, set_take_append l k (by simpa using hk) rest x]

section Step
variable {P Op' Tau' Op Tau : Type} [DecidableEq Tau] (R : Repr Op' Tau' Op Tau)

/-- An extracted `Traced` implementation that computes a model instance `I` through `R`: `step`
    and `accept` agree, and `Tau'`'s clone and equality are honest. -/
structure TracedSpec (R : Repr Op' Tau' Op Tau) (inst : formalism.scheme.Traced P Op' Tau')
    (p : P) (I : Traced Op Tau) (ok : Op → List Tau → Prop) : Prop where
  eq : EqSpec inst.corecmpPartialEqInst
  clone : ∀ a : Tau', inst.corecloneCloneInst.clone a ⦃ (r : Tau') => r = a ⦄
  /-- `step` computes the model's, on the operations and child traces `ok` admits (where the
      model's `run` calls it: `StepsOk`); elsewhere the Rust may fail, e.g. indexing a child. -/
  step : ∀ (op : Op') (s : Slice Tau'), ok (R.opOf op) (s.val.map R.tauOf) →
    inst.step p op s ⦃ (outs : alloc.vec.Vec (Tau' × alloc.vec.Vec (U32 × U32))) =>
      outs.val.map (fun o => (R.tauOf o.1, ofPairs o.2.val)) =
        I.step (R.opOf op) (s.val.map R.tauOf) ⦄
  accept : ∀ t : Tau', inst.accept p t ⦃ (b : Bool) => b = I.accept (R.tauOf t) ⦄

/-- The children's tables, read back. -/
def tablesOf (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau'))) :
    List (List (Tau × Expr)) :=
  cts.val.map (tableOf R)

/-- A digit vector, read back. -/
def idxN (idx : alloc.vec.Vec Usize) : List ℕ := idx.val.map fun i => i.val

omit [DecidableEq Tau] in
theorem length_tableOf (t : alloc.vec.Vec (formalism.scheme.Row Tau')) :
    (tableOf R t).length = t.val.length := by
  simp [tableOf]

omit [DecidableEq Tau] in
theorem length_tablesOf (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau'))) :
    (tablesOf R cts).length = cts.val.length := by
  simp [tablesOf]

theorem length_idxN (idx : alloc.vec.Vec Usize) : (idxN idx).length = idx.val.length := by
  simp [idxN]

/-- The children's table lengths: the odometer's radices. -/
def lensOf (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau'))) : List ℕ :=
  cts.val.map fun t => t.val.length

omit [DecidableEq Tau] in
theorem lens_tablesOf (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau'))) :
    (tablesOf R cts).map List.length = lensOf cts := by
  simp [tablesOf, lensOf, length_tableOf]

omit [DecidableEq Tau] in
theorem length_lensOf (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau'))) :
    (lensOf cts).length = cts.val.length := by
  simp [lensOf]

omit [DecidableEq Tau] in
/-- The model's items at a tuple, in terms of what the extracted `step` returned. -/
theorem rowItems_eq (I : Traced Op Tau) (op : Op') (cur : List (Tau × Expr))
    (outs : alloc.vec.Vec (Tau' × alloc.vec.Vec (U32 × U32)))
    (hstep : outs.val.map (fun o => (R.tauOf o.1, ofPairs o.2.val)) =
      I.step (R.opOf op) (cur.map Prod.fst)) :
    Traced.rowItems I (R.opOf op) cur =
      outs.val.map fun o => (R.tauOf o.1, Expr.joinLeaves (Traced.joined cur) (ofPairs o.2.val)) := by
  rw [Traced.rowItems, ← hstep, List.map_map]
  rfl

/-- What one tuple of rows adds to the table: `stepNode` is its fold over `tuples`. -/
def stepFold (I : Traced Op Tau) (op : Op) (T : List (Tau × Expr)) (rows : List (Tau × Expr)) :
    List (Tau × Expr) :=
  (Traced.rowItems I op rows).foldl (fun T it => Traced.unionInto T it.1 it.2) T

theorem stepNode_eq (I : Traced Op Tau) (op : Op) (L : List (List (Tau × Expr))) :
    Traced.stepNode I op L = (tuples L).foldl (stepFold I op) [] := rfl

theorem length_le_foldl_stepFold (I : Traced Op Tau) (op : Op) :
    ∀ (rows : List (List (Tau × Expr))) (T : List (Tau × Expr)),
      T.length ≤ (rows.foldl (stepFold I op) T).length
  | [], _ => le_rfl
  | r :: rows, T => by
    rw [List.foldl_cons]
    exact (length_le_foldl_unionInto (Traced.rowItems I op r) T).trans
      (length_le_foldl_stepFold I op rows _)

/-! ## Loop 0: the digit vector starts at zero, and is any child table empty -/

omit [DecidableEq Tau] in
theorem step_node_loop0_spec (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau')))
    (n : Usize) (hn : n.val = cts.val.length) (idx : alloc.vec.Vec Usize) (any_empty : Bool)
    (k : Usize) (hk : k.val ≤ n.val) (hidx : idxN idx = List.replicate k.val 0)
    (hany : any_empty = true ↔
      ∃ j, ∃ (hj : j < cts.val.length), j < k.val ∧ (cts.val[j]).val.length = 0) :
    formalism.scheme.step_node_loop0 cts n idx any_empty k
      ⦃ (idx' : alloc.vec.Vec Usize) (any' : Bool) =>
        idxN idx' = List.replicate n.val 0 ∧
        (any' = true ↔ ∃ t ∈ cts.val, t.val.length = 0) ⦄ := by
  unfold formalism.scheme.step_node_loop0
  apply loop.spec_decr_nat (measure := fun s => n.val - s.2.2.val)
    (inv := fun s => s.2.2.val ≤ n.val ∧ idxN s.1 = List.replicate s.2.2.val 0 ∧
      (s.2.1 = true ↔
        ∃ j, ∃ (hj : j < cts.val.length), j < s.2.2.val ∧ (cts.val[j]).val.length = 0))
  · rintro ⟨idx1, any1, k1⟩ ⟨hk1, hidx1, hany1⟩
    replace hk1 : k1.val ≤ n.val := hk1
    replace hidx1 : idxN idx1 = List.replicate k1.val 0 := hidx1
    replace hany1 : any1 = true ↔
      ∃ j, ∃ (hj : j < cts.val.length), j < k1.val ∧ (cts.val[j]).val.length = 0 := hany1
    unfold formalism.scheme.step_node_loop0.body
    simp only [alloc.vec.Vec.index_slice_index]
    split
    · rename_i hlt
      have hlt' : k1.val < cts.val.length := by scalar_tac
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec cts k1 hlt')
      intro v hv
      replace hv : v = cts.val[k1.val] := hv
      simp only [alloc.vec.Vec.is_empty]
      apply WP.spec_bind ((WP.spec_ok (p := fun b => b = decide (v.length = 0)) _).mpr rfl)
      intro b hb
      replace hb : b = decide (v.length = 0) := hb
      have hidxlen : idx1.length < Usize.max := by
        have : (idxN idx1).length = k1.val := by rw [hidx1, List.length_replicate]
        rw [length_idxN] at this
        scalar_tac
      have hpush := alloc.vec.Vec.push_spec idx1 0#usize hidxlen
      have hadd := Usize.add_spec (x := k1) (y := 1#usize) (by scalar_tac)
      by_cases hb' : b = true
      · rw [ite_eq_left hb']
        apply WP.spec_bind ((WP.spec_ok (p := fun a => a = true) _).mpr rfl)
        intro any2 hany2
        replace hany2 : any2 = true := hany2
        subst any2
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
          rw [idxN] at hidx1
          rw [hidx1]
          simp
        · simp only [true_iff]
          refine ⟨k1.val, hlt', by rw [hk2']; exact Nat.lt_succ_self _, ?_⟩
          rw [hb, decide_eq_true_eq] at hb'
          rw [← hv]
          exact hb'
      · rw [ite_eq_right hb']
        apply WP.spec_bind ((WP.spec_ok (p := fun a => a = any1) _).mpr rfl)
        intro any2 hany2
        replace hany2 : any2 = any1 := hany2
        subst any2
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
          rw [idxN] at hidx1
          rw [hidx1]
          simp
        · rw [hany1]
          constructor
          · rintro ⟨j, hj, hjk, hj0⟩
            exact ⟨j, hj, by rw [hk2']; exact Nat.lt_succ_of_lt hjk, hj0⟩
          · rintro ⟨j, hj, hjk, hj0⟩
            rw [hk2'] at hjk
            rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hjk | rfl
            · exact ⟨j, hj, hjk, hj0⟩
            · exfalso
              rw [← hv] at hj0
              rw [hb, decide_eq_true_eq] at hb'
              exact hb' hj0
    · rename_i hge
      have hkn : k1.val = n.val := by scalar_tac
      simp only [WP.spec_ok, WP.uncurry'_pair]
      refine ⟨by rw [hidx1, hkn], ?_⟩
      rw [hany1]
      constructor
      · rintro ⟨j, hj, _, hj0⟩
        exact ⟨_, List.getElem_mem hj, hj0⟩
      · rintro ⟨t, ht, ht0⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
        exact ⟨j, hj, by rw [hkn, hn]; exact hj, ht0⟩
  · exact ⟨hk, hidx, hany⟩

/-! ## Loop 1.0: the traces and the join of the current tuple of rows -/

/-- The current tuple of rows, as the odometer lemma describes it: at each child, the row the
    digit addresses. -/
def CurOf (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau')))
    (idx : alloc.vec.Vec Usize) (cur : List (Tau × Expr)) : Prop :=
  List.Forall₂ (fun (r : Tau × Expr) (p : List (Tau × Expr) × ℕ) => p.1[p.2]? = some r) cur
    ((tablesOf R cts).zip (idxN idx))

omit [DecidableEq Tau] in
theorem CurOf.length {cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau'))}
    {idx : alloc.vec.Vec Usize} {cur : List (Tau × Expr)} (h : CurOf R cts idx cur)
    (hlen : idx.val.length = cts.val.length) : cur.length = cts.val.length := by
  have := List.Forall₂.length_eq h
  rw [List.length_zip, length_tablesOf, length_idxN, hlen, Nat.min_self] at this
  exact this

omit [DecidableEq Tau] in
theorem CurOf.getElem {cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau'))}
    {idx : alloc.vec.Vec Usize} {cur : List (Tau × Expr)} (h : CurOf R cts idx cur)
    (hlen : idx.val.length = cts.val.length) (k : ℕ) (hk : k < cts.val.length) :
    ∃ (hi : (idx.val[k]'(by rw [hlen]; exact hk)).val < (cts.val[k]).val.length),
      cur[k]'(by rw [CurOf.length R h hlen]; exact hk) =
        rowOf R ((cts.val[k]).val[(idx.val[k]'(by rw [hlen]; exact hk)).val]'hi) := by
  have hz : k < ((tablesOf R cts).zip (idxN idx)).length := by
    rw [List.length_zip, length_tablesOf, length_idxN, hlen, Nat.min_self]
    exact hk
  have hr := forall₂_getElem h k (by rw [CurOf.length R h hlen]; exact hk) hz
  simp only [List.getElem_zip, tablesOf, idxN, List.getElem_map, tableOf] at hr
  rw [List.getElem?_map] at hr
  rcases hget : (cts.val[k]).val[(idx.val[k]'(by rw [hlen]; exact hk)).val]? with _ | row
  · rw [hget] at hr
    simp at hr
  · rw [hget] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    obtain ⟨hi, hrow⟩ := List.getElem?_eq_some_iff.mp hget
    exact ⟨hi, by rw [← hr, hrow]⟩

theorem step_node_loop1_loop0_spec (inst : formalism.scheme.Traced P Op' Tau') (p : P)
    (I : Traced Op Tau) {okP : Op → List Tau → Prop} (hI : TracedSpec R inst p I okP)
    (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau'))) (n : Usize)
    (hn : n.val = cts.val.length) (idx : alloc.vec.Vec Usize)
    (hlen : idx.val.length = cts.val.length)
    (cur : List (Tau × Expr)) (hcur : CurOf R cts idx cur)
    (traces : alloc.vec.Vec Tau') (joined : formalism.expr.Expr) (k : Usize) (hk : k.val ≤ n.val)
    (htr : traces.val.map R.tauOf = (cur.take k.val).map Prod.fst)
    (hj : ofExt joined = (cur.take k.val).foldl (fun acc r => Expr.join' acc r.2) .unit) :
    formalism.scheme.step_node_loop1_loop0 inst cts n idx traces joined k
      ⦃ (traces' : alloc.vec.Vec Tau') (joined' : formalism.expr.Expr) =>
        traces'.val.map R.tauOf = cur.map Prod.fst ∧ ofExt joined' = Traced.joined cur ⦄ := by
  unfold formalism.scheme.step_node_loop1_loop0
  apply loop.spec_decr_nat (measure := fun s => n.val - s.2.2.val)
    (inv := fun s => s.2.2.val ≤ n.val ∧ s.1.val.map R.tauOf = (cur.take s.2.2.val).map Prod.fst ∧
      ofExt s.2.1 = (cur.take s.2.2.val).foldl (fun acc r => Expr.join' acc r.2) .unit)
  · rintro ⟨traces1, joined1, k1⟩ ⟨hk1, htr1, hj1⟩
    replace hk1 : k1.val ≤ n.val := hk1
    replace htr1 : traces1.val.map R.tauOf = (cur.take k1.val).map Prod.fst := htr1
    replace hj1 : ofExt joined1 = (cur.take k1.val).foldl (fun acc r => Expr.join' acc r.2) .unit :=
      hj1
    unfold formalism.scheme.step_node_loop1_loop0.body
    simp only [alloc.vec.Vec.index_slice_index]
    split
    · rename_i hlt
      have hlt' : k1.val < cts.val.length := by scalar_tac
      have hlt'' : k1.val < idx.val.length := by rw [hlen]; exact hlt'
      have hcurlen : k1.val < cur.length := by rw [CurOf.length R hcur hlen]; exact hlt'
      obtain ⟨hi, hcurk⟩ := CurOf.getElem R hcur hlen k1.val hlt'
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec cts k1 hlt')
      intro v hv
      replace hv : v = cts.val[k1.val] := hv
      subst v
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec idx k1 hlt'')
      intro i hi'
      replace hi' : i = idx.val[k1.val] := hi'
      subst i
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec _ _ hi)
      intro row hrow
      replace hrow : row = (cts.val[k1.val]).val[(idx.val[k1.val]).val] := hrow
      apply WP.spec_bind (hI.clone row.tau)
      intro t ht
      replace ht : t = row.tau := ht
      subst t
      have htrlen : traces1.length < Usize.max := by
        have h : traces1.val.length = k1.val := by
          have h := congrArg List.length htr1
          rw [List.length_map, List.length_map, List.length_take,
            Nat.min_eq_left hcurlen.le] at h
          exact h
        show traces1.val.length < Usize.max
        rw [h]
        scalar_tac
      apply WP.spec_bind (alloc.vec.Vec.push_spec traces1 row.tau htrlen)
      intro traces2 htr2
      replace htr2 : traces2.val = traces1.val ++ [row.tau] := htr2
      apply WP.spec_bind (clone_spec row.expr)
      intro e he
      replace he : e = row.expr := he
      subst e
      apply WP.spec_bind (join_spec joined1 row.expr)
      intro joined2 hj2
      replace hj2 : ofExt joined2 = Expr.join' (ofExt joined1) (ofExt row.expr) := hj2
      apply WP.spec_bind (Usize.add_spec (x := k1) (y := 1#usize) (by scalar_tac))
      intro k2 hk2
      replace hk2 : k2.val = k1.val + (1#usize).val := hk2
      have hk2' : k2.val = k1.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      have hrowk : cur[k1.val]'hcurlen = rowOf R row := by
        rw [hcurk, hrow]
      have htake : cur.take (k1.val + 1) = cur.take k1.val ++ [cur[k1.val]'hcurlen] :=
        List.take_succ_eq_append_getElem hcurlen
      refine ⟨⟨by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
      · rw [htr2, List.map_append, htr1, hk2', htake, List.map_append, hrowk]
        rfl
      · rw [hj2, hj1, hk2', htake, List.foldl_append, List.foldl_cons, List.foldl_nil, hrowk]
        rfl
    · rename_i hge
      have hkn : k1.val = n.val := by scalar_tac
      have htake : cur.take k1.val = cur :=
        List.take_of_length_le (by rw [CurOf.length R hcur hlen, ← hn, hkn])
      simp only [WP.spec_ok, WP.uncurry'_pair]
      rw [htr1, hj1, htake]
      exact ⟨rfl, rfl⟩
  · exact ⟨hk, htr, hj⟩

/-! ## Loop 1.1: every output of `step` goes into the table -/

theorem step_node_loop1_loop1_spec (inst : formalism.scheme.Traced P Op' Tau') (p : P)
    (I : Traced Op Tau) {okP : Op → List Tau → Prop} (hI : TracedSpec R inst p I okP)
    (table : alloc.vec.Vec (formalism.scheme.Row Tau')) (joined : formalism.expr.Expr)
    (J : Expr) (hJ : ofExt joined = J)
    (outs : alloc.vec.Vec (Tau' × alloc.vec.Vec (U32 × U32))) (T0 : List (Tau × Expr))
    (hfin : ((outs.val.map fun o => (R.tauOf o.1, Expr.joinLeaves J (ofPairs o.2.val))).foldl
      (fun T it => Traced.unionInto T it.1 it.2) T0).length < Usize.max)
    (o : Usize) (ho : o.val ≤ outs.val.length)
    (htab : tableOf R table =
      ((outs.val.map fun o => (R.tauOf o.1, Expr.joinLeaves J (ofPairs o.2.val))).take o.val).foldl
        (fun T it => Traced.unionInto T it.1 it.2) T0) :
    formalism.scheme.step_node_loop1_loop1 inst table joined outs o
      ⦃ (table' : alloc.vec.Vec (formalism.scheme.Row Tau')) =>
        tableOf R table' =
          (outs.val.map fun o => (R.tauOf o.1, Expr.joinLeaves J (ofPairs o.2.val))).foldl
            (fun T it => Traced.unionInto T it.1 it.2) T0 ⦄ := by
  unfold formalism.scheme.step_node_loop1_loop1
  apply loop.spec_decr_nat (measure := fun s => outs.val.length - s.2.val)
    (inv := fun s => s.2.val ≤ outs.val.length ∧ tableOf R s.1 =
      ((outs.val.map fun o => (R.tauOf o.1, Expr.joinLeaves J (ofPairs o.2.val))).take s.2.val).foldl
        (fun T it => Traced.unionInto T it.1 it.2) T0)
  · rintro ⟨table1, o1⟩ ⟨ho1, htab1⟩
    replace ho1 : o1.val ≤ outs.val.length := ho1
    replace htab1 : tableOf R table1 =
      ((outs.val.map fun o => (R.tauOf o.1, Expr.joinLeaves J (ofPairs o.2.val))).take o1.val).foldl
        (fun T it => Traced.unionInto T it.1 it.2) T0 := htab1
    unfold formalism.scheme.step_node_loop1_loop1.body
    simp only [alloc.vec.Vec.index_slice_index]
    split
    · rename_i hlt
      have hlt' : o1.val < outs.val.length := by scalar_tac
      have hlt'' : o1.val <
          (outs.val.map fun o => (R.tauOf o.1, Expr.joinLeaves J (ofPairs o.2.val))).length := by
        rw [List.length_map]
        exact hlt'
      apply WP.spec_bind (clone_spec joined)
      intro e he
      replace he : e = joined := he
      subst e
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec outs o1 hlt')
      rintro ⟨t, v⟩ htv
      replace htv : (t, v) = outs.val[o1.val] := htv
      try dsimp only
      apply WP.spec_bind (join_leaves_spec joined (alloc.vec.Vec.deref v))
      intro e1 he1
      replace he1 : ofExt e1 =
        Expr.joinLeaves (ofExt joined) (ofPairs (alloc.vec.Vec.deref v).val) := he1
      have hvv : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
      rw [hJ, hvv] at he1
      apply WP.spec_bind (hI.clone t)
      intro t1 ht1
      replace ht1 : t1 = t := ht1
      subst t1
      have hlen1 : table1.length < Usize.max := by
        show table1.val.length < Usize.max
        rw [← length_tableOf R, htab1]
        refine lt_of_le_of_lt ?_ hfin
        conv_rhs => rw [← List.take_append_drop o1.val
          (outs.val.map fun o => (R.tauOf o.1, Expr.joinLeaves J (ofPairs o.2.val))),
          List.foldl_append]
        exact length_le_foldl_unionInto _ _
      apply WP.spec_bind (union_into_spec R inst.corecmpPartialEqInst hI.eq table1 t e1 hlen1)
      intro table2 htab2
      replace htab2 : tableOf R table2 =
        Traced.unionInto (tableOf R table1) (R.tauOf t) (ofExt e1) := htab2
      apply WP.spec_bind (Usize.add_spec (x := o1) (y := 1#usize) (by scalar_tac))
      intro o2 ho2
      replace ho2 : o2.val = o1.val + (1#usize).val := ho2
      have ho2' : o2.val = o1.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      rw [htab2, htab1, he1, ho2', List.take_succ_eq_append_getElem hlt'', List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.getElem_map, ← htv]
    · rename_i hge
      have htake :
          (outs.val.map fun o => (R.tauOf o.1, Expr.joinLeaves J (ofPairs o.2.val))).take o1.val =
            outs.val.map fun o => (R.tauOf o.1, Expr.joinLeaves J (ofPairs o.2.val)) :=
        List.take_of_length_le (by rw [List.length_map]; scalar_tac)
      simp only [WP.spec_ok]
      rw [htab1, htake]
  · exact ⟨ho, htab⟩

/-! ## Loop 1.2: the odometer -/

omit [DecidableEq Tau] in
theorem step_node_loop1_loop2_spec (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau')))
    (idx₀ : alloc.vec.Vec Usize) (hlen₀ : idx₀.val.length = cts.val.length)
    (hvalid : ∀ j, (hj : j < cts.val.length) →
      (idx₀.val[j]'(by rw [hlen₀]; exact hj)).val < (cts.val[j]).val.length)
    (idx : alloc.vec.Vec Usize) (k : Usize) (carry : Bool) (hk : k.val ≤ cts.val.length)
    (hlen : idx.val.length = cts.val.length)
    (hidx : idxN idx = (idxN idx₀).take k.val ++
      (incr ((lensOf cts).drop k.val) ((idxN idx₀).drop k.val)).1)
    (hcarry : carry = (incr ((lensOf cts).drop k.val) ((idxN idx₀).drop k.val)).2) :
    formalism.scheme.step_node_loop1_loop2 cts idx k carry
      ⦃ (idx' : alloc.vec.Vec Usize) (carry' : Bool) =>
        idx'.val.length = cts.val.length ∧ idxN idx' = (incr (lensOf cts) (idxN idx₀)).1 ∧
        carry' = (incr (lensOf cts) (idxN idx₀)).2 ⦄ := by
  have hlens := length_lensOf cts
  have hidxs : (idxN idx₀).length = cts.val.length := by rw [length_idxN, hlen₀]
  unfold formalism.scheme.step_node_loop1_loop2
  apply loop.spec_decr_nat (measure := fun s => s.2.1.val)
    (inv := fun s => s.2.1.val ≤ cts.val.length ∧ s.1.val.length = cts.val.length ∧
      idxN s.1 = (idxN idx₀).take s.2.1.val ++
        (incr ((lensOf cts).drop s.2.1.val) ((idxN idx₀).drop s.2.1.val)).1 ∧
      s.2.2 = (incr ((lensOf cts).drop s.2.1.val) ((idxN idx₀).drop s.2.1.val)).2)
  · rintro ⟨idx1, k1, carry1⟩ ⟨hk1, hlen1, hidx1, hcarry1⟩
    replace hk1 : k1.val ≤ cts.val.length := hk1
    replace hlen1 : idx1.val.length = cts.val.length := hlen1
    replace hidx1 : idxN idx1 = (idxN idx₀).take k1.val ++
      (incr ((lensOf cts).drop k1.val) ((idxN idx₀).drop k1.val)).1 := hidx1
    replace hcarry1 : carry1 = (incr ((lensOf cts).drop k1.val) ((idxN idx₀).drop k1.val)).2 :=
      hcarry1
    unfold formalism.scheme.step_node_loop1_loop2.body
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
    split
    · -- still carrying
      rename_i hc
      split
      · -- a digit is left
        rename_i hpos
        have hpos' : 0 < k1.val := by scalar_tac
        apply WP.spec_bind (Usize.sub_spec (x := k1) (y := 1#usize) (by scalar_tac))
        intro k2 hk2
        have hk1eq : k1.val = k2.val + 1 := by scalar_tac
        clear hk2
        have hk2lt : k2.val < cts.val.length := by omega
        have hk2idx : k2.val < idx1.val.length := by rw [hlen1]; exact hk2lt
        have hk2idx₀ : k2.val < idx₀.val.length := by rw [hlen₀]; exact hk2lt
        apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec idx1 k2 hk2idx)
        rintro ⟨i, back⟩ hp
        have hp' : i = idx1.val[k2.val] ∧ back = idx1.set k2 := hp
        obtain ⟨hi, hback⟩ := hp'
        subst back
        try dsimp only
        -- the digit is the original one, below its radix
        have hi0 : i.val = (idx₀.val[k2.val]'hk2idx₀).val := by
          have h1 : (idxN idx1)[k2.val]? = some i.val := by
            rw [idxN, List.getElem?_map, List.getElem?_eq_getElem hk2idx, Option.map_some, ← hi]
          rw [hidx1, List.getElem?_append_left (by rw [List.length_take, hidxs]; omega),
            getElem?_take_of_lt' _ _ _ (by omega), idxN, List.getElem?_map,
            List.getElem?_eq_getElem hk2idx₀, Option.map_some, Option.some.injEq] at h1
          exact h1.symm
        have hi_lt : i.val < (cts.val[k2.val]).val.length := by
          rw [hi0]
          exact hvalid k2.val hk2lt
        apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
        intro i1 hi1
        replace hi1 : i1.val = i.val + (1#usize).val := hi1
        have hi1' : i1.val = i.val + 1 := by scalar_tac
        try dsimp only
        have hk2set : k2.val < (idx1.set k2 i1).length := by
          show k2.val < (idx1.set k2 i1).val.length
          rw [alloc.vec.Vec.set_val_eq, List.length_set]
          exact hk2idx
        apply WP.spec_bind (alloc.vec.Vec.index_usize_spec (idx1.set k2 i1) k2 hk2set)
        intro i2 hi2
        replace hi2 : i2 = (idx1.set k2 i1).val[k2.val] := hi2
        have hi2' : i2 = i1 := by
          rw [hi2]
          simp [alloc.vec.Vec.set_val_eq]
        subst i2
        apply WP.spec_bind (alloc.vec.Vec.index_usize_spec cts k2 hk2lt)
        intro v hv
        replace hv : v = cts.val[k2.val] := hv
        -- the model's step at this digit
        have hdropl : (lensOf cts).drop k2.val =
            (cts.val[k2.val]).val.length :: (lensOf cts).drop k1.val := by
          rw [lensOf, map_drop', map_drop', List.drop_eq_getElem_cons hk2lt, hk1eq, List.map_cons]
        have hdropi : (idxN idx₀).drop k2.val =
            (idx₀.val[k2.val]'hk2idx₀).val :: (idxN idx₀).drop k1.val := by
          rw [idxN, map_drop', map_drop', List.drop_eq_getElem_cons hk2idx₀, hk1eq, List.map_cons]
        have hcarry_true :
            (incr ((lensOf cts).drop k1.val) ((idxN idx₀).drop k1.val)).2 = true := by
          rw [← hcarry1]
          simpa using hc
        have hset1 : idxN (idx1.set k2 i1) = (idxN idx₀).take k2.val ++ i1.val ::
            (incr ((lensOf cts).drop k1.val) ((idxN idx₀).drop k1.val)).1 := by
          rw [idxN, alloc.vec.Vec.set_val_eq, List.map_set]
          show (idxN idx1).set k2.val i1.val = _
          rw [hidx1, hk1eq, set_take_append _ _ (by rw [hidxs]; exact hk2lt)]
        split
        · -- the digit advances: no carry
          rename_i hlt
          have hlt' : i.val + 1 < (cts.val[k2.val]).val.length := by
            rw [← hi1', ← hv]
            scalar_tac
          rw [hi0] at hlt'
          simp only [WP.spec_ok]
          refine ⟨⟨by scalar_tac, ?_, ?_, ?_⟩, by scalar_tac⟩
          · show (idx1.set k2 i1).val.length = cts.val.length
            rw [alloc.vec.Vec.set_val_eq, List.length_set, hlen1]
          · rw [hset1, hdropl, hdropi, hi1', hi0]
            simp only [incr, hcarry_true, ite_true]
            rw [ite_eq_left hlt']
          · rw [hdropl, hdropi]
            simp only [incr, hcarry_true, ite_true]
            rw [ite_eq_left hlt']
        · -- the digit wraps: carry on
          rename_i hge
          have hge' : ¬ i.val + 1 < (cts.val[k2.val]).val.length := by
            rw [← hi1', ← hv]
            scalar_tac
          rw [hi0] at hge'
          have h0 : (0#usize).val = 0 := by scalar_tac
          apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec (idx1.set k2 i1) k2 hk2set)
          rintro ⟨_, back1⟩ hp
          have hp' : back1 = (idx1.set k2 i1).set k2 := hp.2
          subst back1
          show WP.spec (ok (ControlFlow.cont _)) _
          simp only [WP.spec_ok]
          refine ⟨⟨by scalar_tac, ?_, ?_, ?_⟩, by scalar_tac⟩
          · show ((idx1.set k2 i1).set k2 0#usize).val.length = cts.val.length
            rw [alloc.vec.Vec.set_val_eq, List.length_set, alloc.vec.Vec.set_val_eq,
              List.length_set, hlen1]
          · rw [idxN, alloc.vec.Vec.set_val_eq, List.map_set, alloc.vec.Vec.set_val_eq,
              List.map_set, List.set_set]
            show (idxN idx1).set k2.val (0#usize).val = _
            rw [hidx1, hk1eq, set_take_append _ _ (by rw [hidxs]; exact hk2lt), hdropl, hdropi, h0]
            simp only [incr, hcarry_true, ite_true]
            rw [ite_eq_right hge', hk1eq]
          · rw [hdropl, hdropi]
            simp only [incr, hcarry_true, ite_true]
            rw [ite_eq_right hge']
            simpa using hc
      · -- no digit left: the whole vector wrapped
        rename_i hzero
        have hzero' : k1.val = 0 := by scalar_tac
        simp only [WP.spec_ok, WP.uncurry'_pair]
        rw [hzero', List.drop_zero, List.drop_zero] at hcarry1
        rw [hzero', List.drop_zero, List.drop_zero, List.take_zero, List.nil_append] at hidx1
        exact ⟨hlen1, hidx1, hcarry1⟩
    · -- the carry stopped: digits below were left alone
      rename_i hnc
      have hnc' : carry1 = false := by simpa using hnc
      rw [hnc'] at hcarry1
      simp only [WP.spec_ok, WP.uncurry'_pair]
      have h := incr_append_of_not_carry ((lensOf cts).take k1.val) ((idxN idx₀).take k1.val)
        ((lensOf cts).drop k1.val) ((idxN idx₀).drop k1.val)
        (by rw [List.length_take, List.length_take, hlens, hidxs]) hcarry1.symm
      rw [List.take_append_drop, List.take_append_drop] at h
      rw [h]
      exact ⟨hlen1, hidx1, hnc'⟩
  · exact ⟨hk, hlen, hidx, hcarry⟩

/-! ## Loop 1: the outer loop walks `tuples` -/

theorem step_node_loop1_spec (inst : formalism.scheme.Traced P Op' Tau') (p : P)
    (I : Traced Op Tau) {okP : Op → List Tau → Prop} (hI : TracedSpec R inst p I okP) (op : Op')
    (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau'))) (n : Usize)
    (hn : n.val = cts.val.length)
    (hfin : (Traced.stepNode I (R.opOf op) (tablesOf R cts)).length < Usize.max)
    (hok : ∀ cur ∈ tuples (tablesOf R cts), okP (R.opOf op) (cur.map Prod.fst))
    (table : alloc.vec.Vec (formalism.scheme.Row Tau')) (idx : alloc.vec.Vec Usize) (done1 : Bool)
    (hinv : if done1 then tableOf R table = Traced.stepNode I (R.opOf op) (tablesOf R cts)
      else Valid (tablesOf R cts) (idxN idx) ∧ idx.val.length = cts.val.length ∧
        ∃ pre, tuples (tablesOf R cts) = pre ++ rest (tablesOf R cts) (idxN idx) ∧
          tableOf R table = pre.foldl (stepFold I (R.opOf op)) []) :
    formalism.scheme.step_node_loop1 inst p op cts table n idx done1
      ⦃ (table' : alloc.vec.Vec (formalism.scheme.Row Tau')) =>
        tableOf R table' = Traced.stepNode I (R.opOf op) (tablesOf R cts) ⦄ := by
  unfold formalism.scheme.step_node_loop1
  apply loop.spec_decr_nat
    (measure := fun s => if s.2.2 then 0 else (rest (tablesOf R cts) (idxN s.2.1)).length)
    (inv := fun s => if s.2.2 then tableOf R s.1 = Traced.stepNode I (R.opOf op) (tablesOf R cts)
      else Valid (tablesOf R cts) (idxN s.2.1) ∧ s.2.1.val.length = cts.val.length ∧
        ∃ pre, tuples (tablesOf R cts) = pre ++ rest (tablesOf R cts) (idxN s.2.1) ∧
          tableOf R s.1 = pre.foldl (stepFold I (R.opOf op)) [])
  · rintro ⟨table1, idx1, done2⟩ hinv1
    try simp only at hinv1
    unfold formalism.scheme.step_node_loop1.body
    cases done2 with
    | true =>
      rw [ite_eq_left rfl] at hinv1
      simp only [ite_true, WP.spec_ok]
      exact hinv1
    | false =>
      rw [ite_eq_right Bool.false_ne_true] at hinv1
      obtain ⟨hvalid, hlen1, pre, hsplit, htab1⟩ := hinv1
      simp only [Bool.false_eq_true, ite_false]
      obtain ⟨cur, hcur, hrest⟩ := rest_incr (tablesOf R cts) (idxN idx1) hvalid
      rw [lens_tablesOf] at hrest
      have hcur' : CurOf R cts idx1 cur := hcur
      -- the tuple just visited sits at the head of the rest, whichever way it ends
      have htail : ∃ tail, rest (tablesOf R cts) (idxN idx1) = cur :: tail := by
        rcases hc : (incr (lensOf cts) (idxN idx1)).2
        · rw [hc, ite_eq_right Bool.false_ne_true] at hrest
          exact ⟨_, hrest.1⟩
        · rw [hc, ite_eq_left rfl] at hrest
          exact ⟨[], hrest⟩
      obtain ⟨tail, htail⟩ := htail
      -- the target is the fold of the rest from here, so every intermediate table is shorter
      have htarget : Traced.stepNode I (R.opOf op) (tablesOf R cts) =
          tail.foldl (stepFold I (R.opOf op)) (stepFold I (R.opOf op) (tableOf R table1) cur) := by
        rw [stepNode_eq, hsplit, htail, List.foldl_append, List.foldl_cons, htab1]
      have hfin' : (stepFold I (R.opOf op) (tableOf R table1) cur).length < Usize.max := by
        refine lt_of_le_of_lt ?_ hfin
        rw [htarget]
        exact length_le_foldl_stepFold I (R.opOf op) tail _
      apply WP.spec_bind (step_node_loop1_loop0_spec R inst p I hI cts n hn idx1 hlen1 cur hcur'
        (alloc.vec.Vec.new Tau') formalism.expr.Expr.Unit 0#usize (by scalar_tac)
        (by simp [alloc.vec.Vec.new]) (by simp [ofExt]))
      rintro ⟨traces, joined⟩ hp
      have hp' : traces.val.map R.tauOf = cur.map Prod.fst ∧ ofExt joined = Traced.joined cur := hp
      obtain ⟨htr, hj⟩ := hp'
      try dsimp only
      have hs : (alloc.vec.Vec.deref traces).val.map R.tauOf = cur.map Prod.fst := by
        simp [alloc.vec.Vec.deref, htr]
      have hcurmem : cur ∈ tuples (tablesOf R cts) := by
        rw [hsplit, htail]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      apply WP.spec_bind (hI.step op (alloc.vec.Vec.deref traces) (by rw [hs]; exact hok cur hcurmem))
      intro outs houts
      replace houts : outs.val.map (fun o => (R.tauOf o.1, ofPairs o.2.val)) =
        I.step (R.opOf op) ((alloc.vec.Vec.deref traces).val.map R.tauOf) := houts
      rw [hs] at houts
      have hitems := rowItems_eq R I op cur outs houts
      have hfold : (outs.val.map fun o =>
          (R.tauOf o.1, Expr.joinLeaves (Traced.joined cur) (ofPairs o.2.val))).foldl
            (fun T it => Traced.unionInto T it.1 it.2) (tableOf R table1) =
          stepFold I (R.opOf op) (tableOf R table1) cur := by
        rw [stepFold, hitems]
      apply WP.spec_bind (step_node_loop1_loop1_spec R inst p I hI table1 joined
        (Traced.joined cur) hj outs (tableOf R table1) (by rw [hfold]; exact hfin') 0#usize
        (by scalar_tac) (by simp))
      intro table2 htab2
      replace htab2 : tableOf R table2 = (outs.val.map fun o =>
          (R.tauOf o.1, Expr.joinLeaves (Traced.joined cur) (ofPairs o.2.val))).foldl
            (fun T it => Traced.unionInto T it.1 it.2) (tableOf R table1) := htab2
      rw [hfold] at htab2
      -- the odometer
      have hvalid' : ∀ j, (hj : j < cts.val.length) →
          (idx1.val[j]'(by rw [hlen1]; exact hj)).val < (cts.val[j]).val.length := by
        intro j hj
        have h := forall₂_getElem hvalid j (by rw [length_idxN, hlen1]; exact hj)
          (by rw [length_tablesOf]; exact hj)
        simp only [idxN, tablesOf, List.getElem_map, length_tableOf] at h
        exact h
      have hlens := length_lensOf cts
      have hidxs : (idxN idx1).length = cts.val.length := by rw [length_idxN, hlen1]
      apply WP.spec_bind (step_node_loop1_loop2_spec cts idx1 hlen1 hvalid' idx1 n true
        (by rw [hn]) hlen1
        (by rw [hn, List.drop_eq_nil_of_le hlens.le, List.drop_eq_nil_of_le hidxs.le,
          List.take_of_length_le hidxs.le]; simp [incr])
        (by rw [hn, List.drop_eq_nil_of_le hlens.le, List.drop_eq_nil_of_le hidxs.le]; simp [incr]))
      rintro ⟨idx2, carry⟩ hp
      have hp' : idx2.val.length = cts.val.length ∧ idxN idx2 = (incr (lensOf cts) (idxN idx1)).1 ∧
        carry = (incr (lensOf cts) (idxN idx1)).2 := hp
      obtain ⟨hlen2, hidx2, hcarry⟩ := hp'
      show WP.spec (ok (ControlFlow.cont _)) _
      simp only [WP.spec_ok]
      cases carry with
      | true =>
        rw [← hcarry, ite_eq_left rfl] at hrest
        have htail0 : tail = [] := (List.cons.inj (htail.symm.trans hrest)).2
        simp only [ite_true]
        refine ⟨?_, ?_⟩
        · rw [htarget, htail0, List.foldl_nil]
          exact htab2
        · rw [htail]
          exact Nat.succ_pos _
      | false =>
        rw [← hcarry, ite_eq_right Bool.false_ne_true] at hrest
        obtain ⟨hrest, hvalid2⟩ := hrest
        simp only [Bool.false_eq_true, ite_false]
        rw [← hidx2] at hrest hvalid2
        refine ⟨⟨hvalid2, hlen2, pre ++ [cur], ?_, ?_⟩, ?_⟩
        · rw [hsplit, hrest, List.append_assoc, List.singleton_append]
        · rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← htab1]
          exact htab2
        · rw [hrest]
          exact Nat.lt_succ_self _
  · exact hinv

/-! ## `step_node` -/

/-- `scheme::step_node` computes the model's `stepNode`, when the table it builds fits. -/
theorem step_node_spec (inst : formalism.scheme.Traced P Op' Tau') (p : P)
    (I : Traced Op Tau) {okP : Op → List Tau → Prop} (hI : TracedSpec R inst p I okP) (op : Op')
    (cts : alloc.vec.Vec (alloc.vec.Vec (formalism.scheme.Row Tau')))
    (hfin : (Traced.stepNode I (R.opOf op) (tablesOf R cts)).length < Usize.max)
    (hok : ∀ cur ∈ tuples (tablesOf R cts), okP (R.opOf op) (cur.map Prod.fst)) :
    formalism.scheme.step_node inst p op cts
      ⦃ (t : alloc.vec.Vec (formalism.scheme.Row Tau')) =>
        tableOf R t = Traced.stepNode I (R.opOf op) (tablesOf R cts) ⦄ := by
  unfold formalism.scheme.step_node
  try dsimp only
  have hn : (alloc.vec.Vec.len cts).val = cts.val.length := by simp
  apply WP.spec_bind (step_node_loop0_spec cts (alloc.vec.Vec.len cts) hn
    (alloc.vec.Vec.new Usize) false 0#usize (by scalar_tac) (by simp [idxN, alloc.vec.Vec.new])
    (by simp))
  rintro ⟨idx, any_empty⟩ hp
  have hp' : idxN idx = List.replicate (alloc.vec.Vec.len cts).val 0 ∧
    (any_empty = true ↔ ∃ t ∈ cts.val, t.val.length = 0) := hp
  obtain ⟨hidx, hany⟩ := hp'
  rw [hn] at hidx
  try dsimp only
  have hlen : idx.val.length = cts.val.length := by
    have := congrArg List.length hidx
    rw [length_idxN, List.length_replicate] at this
    exact this
  apply step_node_loop1_spec R inst p I hI op cts (alloc.vec.Vec.len cts) hn hfin hok
    (alloc.vec.Vec.new (formalism.scheme.Row Tau')) idx any_empty
  cases any_empty with
  | true =>
    rw [ite_eq_left rfl]
    obtain ⟨t, ht, ht0⟩ := hany.mp rfl
    have hnil : tuples (tablesOf R cts) = [] :=
      tuples_eq_nil _ ⟨tableOf R t, List.mem_map.mpr ⟨t, ht, rfl⟩,
        List.eq_nil_of_length_eq_zero (by rw [length_tableOf]; exact ht0)⟩
    rw [stepNode_eq, hnil, List.foldl_nil]
    simp [tableOf, alloc.vec.Vec.new]
  | false =>
    rw [ite_eq_right Bool.false_ne_true]
    have hne : ∀ l ∈ tablesOf R cts, l ≠ [] := by
      intro l hl hnil
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
      exact absurd (hany.mpr ⟨t, ht, by rw [← length_tableOf R, hnil]; rfl⟩) (by simp)
    have hL := length_tablesOf R cts
    refine ⟨?_, hlen, [], ?_, ?_⟩
    · rw [hidx, ← hL]
      exact valid_zeros _ hne
    · rw [hidx, ← hL, rest_zeros _ hne, List.nil_append]
    · simp [tableOf, alloc.vec.Vec.new]

end Step

end Formalism.Refine
