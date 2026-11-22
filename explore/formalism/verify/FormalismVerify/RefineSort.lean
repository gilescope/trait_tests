import FormalismVerify.Quicksort
import FormalismVerify.Extracted.Hylo

/-!
# `hylo::sort::quicksort` sorts

The extracted `quicksort` is `hylo_node_tree(Pivot, Concat)`. Through a reading `R : T → α`
of the elements into a linear order, with `Ord::lt` deciding `R x < R y` (`OrdSpec`), it
computes `Quicksort.quicksortBy R` on the vector's list (`quicksort_spec`), so its output is a
permutation of the input whose readings are sorted (`quicksort_sound`). For `u64` the reading is
the value.
-/

namespace Formalism.RefineSort
open Aeneas Aeneas.Std Result hylo Formalism.Quicksort

variable {T α : Type} [LinearOrder α]

/-- An extracted `Ord` whose `lt` decides the order of the readings. -/
def OrdSpec (inst : core.cmp.Ord T) (R : T → α) : Prop :=
  ∀ x y : T, inst.partialOrdInst.lt x y ⦃ (b : Bool) => b = decide (R x < R y) ⦄

/-- The last element of a vector's list and the rest, when there is one. -/
theorem eq_dropLast_append_of_getLast?_eq_some {l : List T} {x : T} (h : l.getLast? = some x) :
    l = l.dropLast ++ [x] := by
  have hne : l ≠ [] := by
    intro hnil
    rw [hnil] at h
    exact absurd h (by simp)
  have hx : l.getLast hne = x := Option.some.inj ((List.getLast?_eq_getLast hne).symm.trans h)
  rw [← hx]
  exact (List.dropLast_append_getLast hne).symm

/-- `Pivot::unfold`'s loop: the popped elements, in pop order, below the pivot to the left and
    the others to the right. -/
theorem unfold_loop_spec (inst : core.cmp.Ord T) (R : T → α) (hO : OrdSpec inst R) (p : T)
    (v l r : alloc.vec.Vec T) (hb : v.val.length + l.val.length + r.val.length < Usize.max) :
    hylo.sort.Pivot.Insts.HyloShapeNodeTreePlanTVec.unfold_loop inst v p l r
      ⦃ (res : alloc.vec.Vec T × alloc.vec.Vec T) =>
        res.1.val = l.val ++ (v.val.reverse.filter fun x => decide (R x < R p)) ∧
        res.2.val = r.val ++ (v.val.reverse.filter fun x => !decide (R x < R p)) ⦄ := by
  unfold hylo.sort.Pivot.Insts.HyloShapeNodeTreePlanTVec.unfold_loop
  apply loop.spec_decr_nat (measure := fun s => s.1.val.length)
    (inv := fun s => s.1.val.length + s.2.1.val.length + s.2.2.val.length < Usize.max ∧
      s.2.1.val ++ (s.1.val.reverse.filter fun x => decide (R x < R p)) =
        l.val ++ (v.val.reverse.filter fun x => decide (R x < R p)) ∧
      s.2.2.val ++ (s.1.val.reverse.filter fun x => !decide (R x < R p)) =
        r.val ++ (v.val.reverse.filter fun x => !decide (R x < R p)))
  · rintro ⟨v1, l1, r1⟩ ⟨hb1, hl1, hr1⟩
    replace hb1 : v1.val.length + l1.val.length + r1.val.length < Usize.max := hb1
    replace hl1 : l1.val ++ (v1.val.reverse.filter fun x => decide (R x < R p)) =
      l.val ++ (v.val.reverse.filter fun x => decide (R x < R p)) := hl1
    replace hr1 : r1.val ++ (v1.val.reverse.filter fun x => !decide (R x < R p)) =
      r.val ++ (v.val.reverse.filter fun x => !decide (R x < R p)) := hr1
    show hylo.sort.Pivot.Insts.HyloShapeNodeTreePlanTVec.unfold_loop.body inst p v1 l1 r1 ⦃ _ ⦄
    unfold hylo.sort.Pivot.Insts.HyloShapeNodeTreePlanTVec.unfold_loop.body
    apply WP.spec_bind (alloc.vec.Vec.pop_spec v1)
    rintro ⟨o, v2⟩ hpop
    have hpop' : o = v1.val.getLast? ∧ v2.val = v1.val.dropLast := hpop
    obtain ⟨ho, hv2⟩ := hpop'
    cases o with
    | none =>
      have hnil : v1.val = [] := List.getLast?_eq_none_iff.mp ho.symm
      show WP.spec (ok (ControlFlow.done (l1, r1))) _
      rw [WP.spec_ok]
      refine ⟨?_, ?_⟩
      · show l1.val = _
        rw [← hl1, hnil, List.reverse_nil, List.filter_nil, List.append_nil]
      · show r1.val = _
        rw [← hr1, hnil, List.reverse_nil, List.filter_nil, List.append_nil]
    | some x =>
      have hv1 : v1.val = v2.val ++ [x] := by
        rw [hv2]
        exact eq_dropLast_append_of_getLast?_eq_some ho.symm
      have hrev : v1.val.reverse = x :: v2.val.reverse := by
        rw [hv1, List.reverse_append, List.reverse_singleton, List.singleton_append]
      have hlen : v1.val.length = v2.val.length + 1 := by
        rw [hv1, List.length_append, List.length_singleton]
      try dsimp only
      apply WP.spec_bind (hO x p)
      intro b hb
      replace hb : b = decide (R x < R p) := hb
      subst hb
      cases hdec : decide (R x < R p) with
      | true =>
        rw [ite_eq_left rfl]
        apply WP.spec_bind (alloc.vec.Vec.push_spec l1 x (by omega))
        intro l2 hl2
        replace hl2 : l2.val = l1.val ++ [x] := hl2
        show WP.spec (ok (ControlFlow.cont (v2, l2, r1))) _
        rw [WP.spec_ok]
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · show v2.val.length + l2.val.length + r1.val.length < Usize.max
          rw [hl2, List.length_append, List.length_singleton]
          omega
        · show l2.val ++ _ = _
          rw [← hl1, hrev, List.filter_cons_of_pos hdec, hl2, List.append_assoc,
            List.singleton_append]
        · show r1.val ++ _ = _
          rw [← hr1, hrev, List.filter_cons_of_neg (by rw [hdec]; rfl)]
        · show v2.val.length < v1.val.length
          omega
      | false =>
        rw [ite_eq_right Bool.false_ne_true]
        apply WP.spec_bind (alloc.vec.Vec.push_spec r1 x (by omega))
        intro r2 hr2
        replace hr2 : r2.val = r1.val ++ [x] := hr2
        show WP.spec (ok (ControlFlow.cont (v2, l1, r2))) _
        rw [WP.spec_ok]
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · show v2.val.length + l1.val.length + r2.val.length < Usize.max
          rw [hr2, List.length_append, List.length_singleton]
          omega
        · show l1.val ++ _ = _
          rw [← hl1, hrev, List.filter_cons_of_neg hdec]
        · show r2.val ++ _ = _
          rw [← hr1, hrev, List.filter_cons_of_pos (by rw [hdec]; rfl), hr2, List.append_assoc,
            List.singleton_append]
        · show v2.val.length < v1.val.length
          omega
  · exact ⟨hb, rfl, rfl⟩

/-- `Pivot::unfold` on an empty vector: no layer. -/
theorem unfold_spec_nil (inst : core.cmp.Ord T) (self : hylo.sort.Pivot) (v : alloc.vec.Vec T)
    (hv : v.val = []) :
    hylo.sort.Pivot.Insts.HyloShapeNodeTreePlanTVec.unfold inst self v
      ⦃ (res : Option (T × alloc.vec.Vec T × alloc.vec.Vec T) × hylo.sort.Pivot) =>
        res.1 = none ⦄ := by
  unfold hylo.sort.Pivot.Insts.HyloShapeNodeTreePlanTVec.unfold
  apply WP.spec_bind (alloc.vec.Vec.pop_spec v)
  rintro ⟨o, v1⟩ hpop
  have hpop' : o = v.val.getLast? ∧ v1.val = v.val.dropLast := hpop
  obtain ⟨ho, _⟩ := hpop'
  rw [hv, List.getLast?_nil] at ho
  subst ho
  show WP.spec (ok (none, self)) _
  rw [WP.spec_ok]
  rfl

/-- `Pivot::unfold` on a vector ending in `p`: the pivot `p` and the partition of the rest,
    read from the back. -/
theorem unfold_spec_cons (inst : core.cmp.Ord T) (R : T → α) (hO : OrdSpec inst R)
    (self : hylo.sort.Pivot) (v : alloc.vec.Vec T) (v' : List T) (p : T) (hv : v.val = v' ++ [p]) :
    hylo.sort.Pivot.Insts.HyloShapeNodeTreePlanTVec.unfold inst self v
      ⦃ (res : Option (T × alloc.vec.Vec T × alloc.vec.Vec T) × hylo.sort.Pivot) =>
        ∃ l r : alloc.vec.Vec T, res.1 = some (p, l, r) ∧
          l.val = v'.reverse.filter (fun x => decide (R x < R p)) ∧
          r.val = v'.reverse.filter (fun x => !decide (R x < R p)) ⦄ := by
  unfold hylo.sort.Pivot.Insts.HyloShapeNodeTreePlanTVec.unfold
  apply WP.spec_bind (alloc.vec.Vec.pop_spec v)
  rintro ⟨o, v1⟩ hpop
  have hpop' : o = v.val.getLast? ∧ v1.val = v.val.dropLast := hpop
  obtain ⟨ho, hv1⟩ := hpop'
  rw [hv, List.getLast?_concat] at ho
  rw [hv, List.dropLast_concat] at hv1
  subst ho
  try dsimp only
  have hb : v1.val.length + (alloc.vec.Vec.new T).val.length + (alloc.vec.Vec.new T).val.length
      < Usize.max := by
    have := v.property
    rw [hv, List.length_append, List.length_singleton] at this
    rw [hv1]
    show v'.length + ([] : List T).length + ([] : List T).length < Usize.max
    simp only [List.length_nil, Nat.add_zero]
    omega
  apply WP.spec_bind (unfold_loop_spec inst R hO p v1 (alloc.vec.Vec.new T) (alloc.vec.Vec.new T) hb)
  rintro ⟨l, r⟩ hlr
  have hlr' : l.val = (alloc.vec.Vec.new T).val ++ (v1.val.reverse.filter fun x => decide (R x < R p)) ∧
      r.val = (alloc.vec.Vec.new T).val ++ (v1.val.reverse.filter fun x => !decide (R x < R p)) := hlr
  obtain ⟨hl, hr⟩ := hlr'
  show WP.spec (ok (some (p, l, r), self)) _
  rw [WP.spec_ok]
  refine ⟨l, r, rfl, ?_, ?_⟩
  · rw [hl, hv1]
    rfl
  · rw [hr, hv1]
    rfl

/-- `Concat::fold`'s loop: pop from `b`, push onto `a`. -/
theorem fold_loop_spec (b a : alloc.vec.Vec T) (hb : a.val.length + b.val.length ≤ Usize.max) :
    hylo.sort.Concat.Insts.HyloShapeNodeTreeAlgebraTVec.fold_loop b a
      ⦃ (res : alloc.vec.Vec T) => res.val = a.val ++ b.val.reverse ⦄ := by
  unfold hylo.sort.Concat.Insts.HyloShapeNodeTreeAlgebraTVec.fold_loop
  apply loop.spec_decr_nat (measure := fun s => s.1.val.length)
    (inv := fun s => s.2.val.length + s.1.val.length ≤ Usize.max ∧
      s.2.val ++ s.1.val.reverse = a.val ++ b.val.reverse)
  · rintro ⟨b1, a1⟩ ⟨hb1, hinv⟩
    replace hb1 : a1.val.length + b1.val.length ≤ Usize.max := hb1
    replace hinv : a1.val ++ b1.val.reverse = a.val ++ b.val.reverse := hinv
    show hylo.sort.Concat.Insts.HyloShapeNodeTreeAlgebraTVec.fold_loop.body b1 a1 ⦃ _ ⦄
    unfold hylo.sort.Concat.Insts.HyloShapeNodeTreeAlgebraTVec.fold_loop.body
    apply WP.spec_bind (alloc.vec.Vec.pop_spec b1)
    rintro ⟨o, b2⟩ hpop
    have hpop' : o = b1.val.getLast? ∧ b2.val = b1.val.dropLast := hpop
    obtain ⟨ho, hb2⟩ := hpop'
    cases o with
    | none =>
      have hnil : b1.val = [] := List.getLast?_eq_none_iff.mp ho.symm
      show WP.spec (ok (ControlFlow.done a1)) _
      rw [WP.spec_ok]
      show a1.val = _
      rw [← hinv, hnil, List.reverse_nil, List.append_nil]
    | some x =>
      have hb1' : b1.val = b2.val ++ [x] := by
        rw [hb2]
        exact eq_dropLast_append_of_getLast?_eq_some ho.symm
      have hlen : b1.val.length = b2.val.length + 1 := by
        rw [hb1', List.length_append, List.length_singleton]
      try dsimp only
      apply WP.spec_bind (alloc.vec.Vec.push_spec a1 x (by omega))
      intro a2 ha2
      replace ha2 : a2.val = a1.val ++ [x] := ha2
      show WP.spec (ok (ControlFlow.cont (b2, a2))) _
      rw [WP.spec_ok]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show a2.val.length + b2.val.length ≤ Usize.max
        rw [ha2, List.length_append, List.length_singleton]
        omega
      · show a2.val ++ b2.val.reverse = _
        rw [← hinv, hb1', List.reverse_append, List.reverse_singleton, List.singleton_append, ha2,
          List.append_assoc, List.singleton_append]
      · show b2.val.length < b1.val.length
        omega
  · exact ⟨hb, rfl⟩

/-- `Concat::fold` on a layer: left, pivot, right. -/
theorem fold_spec_some (self : hylo.sort.Concat) (p : T) (a b : alloc.vec.Vec T)
    (hb : a.val.length + 1 + b.val.length ≤ Usize.max) :
    hylo.sort.Concat.Insts.HyloShapeNodeTreeAlgebraTVec.fold self (some (p, a, b))
      ⦃ (res : alloc.vec.Vec T × hylo.sort.Concat) => res.1.val = a.val ++ p :: b.val ⦄ := by
  unfold hylo.sort.Concat.Insts.HyloShapeNodeTreeAlgebraTVec.fold
  try dsimp only
  apply WP.spec_bind (alloc.vec.Vec.push_spec a p (by omega))
  intro a1 ha1
  replace ha1 : a1.val = a.val ++ [p] := ha1
  apply WP.spec_bind ((WP.spec_ok (p := fun r => r = alloc.vec.Vec.deref_mut b) _).mpr rfl)
  rintro ⟨s, back⟩ hsb
  have hsb' : (s, back) = alloc.vec.Vec.deref_mut b := hsb
  rw [alloc.vec.Vec.deref_mut, Prod.mk.injEq] at hsb'
  obtain ⟨hs, hback⟩ := hsb'
  subst hs hback
  apply WP.spec_bind
    ((WP.spec_ok (p := fun r => r = core.slice.Slice.reverse b.slice) _).mpr rfl)
  intro s1 hs1
  subst hs1
  try dsimp only
  have hb1 : ({ slice := core.slice.Slice.reverse b.slice } : alloc.vec.Vec T).val =
      b.val.reverse := by
    show (core.slice.Slice.reverse b.slice).val = _
    rw [core.slice.Slice.reverse, Slice.from_val]
    rfl
  apply WP.spec_bind (fold_loop_spec { slice := core.slice.Slice.reverse b.slice } a1
    (by rw [hb1, List.length_reverse, ha1, List.length_append, List.length_singleton]; exact hb))
  intro a2 ha2
  replace ha2 : a2.val = a1.val ++ ({ slice := core.slice.Slice.reverse b.slice } :
    alloc.vec.Vec T).val.reverse := ha2
  rw [WP.spec_ok]
  show a2.val = _
  rw [ha2, hb1, List.reverse_reverse, ha1, List.append_assoc, List.singleton_append]

theorem fold_spec_none (self : hylo.sort.Concat) :
    hylo.sort.Concat.Insts.HyloShapeNodeTreeAlgebraTVec.fold (T := T) self none
      ⦃ (res : alloc.vec.Vec T × hylo.sort.Concat) => res.1.val = [] ⦄ := by
  unfold hylo.sort.Concat.Insts.HyloShapeNodeTreeAlgebraTVec.fold
  rw [WP.spec_ok]
  rfl

/-- The hylomorphism computes `quicksortBy R` on the vector's list. -/
theorem hylo_spec (inst : core.cmp.Ord T) (R : T → α) (hO : OrdSpec inst R) :
    ∀ (n : ℕ) (v : alloc.vec.Vec T) (plan : hylo.sort.Pivot) (alg : hylo.sort.Concat),
      v.val.length ≤ n →
      hylo.shape.hylo_node_tree (hylo.sort.Pivot.Insts.HyloShapeNodeTreePlanTVec inst)
        (hylo.sort.Concat.Insts.HyloShapeNodeTreeAlgebraTVec T) plan alg v
        ⦃ (res : alloc.vec.Vec T × hylo.sort.Pivot × hylo.sort.Concat) =>
          res.1.val = quicksortBy R v.val ⦄
  | n, v, plan, alg, hn => by
    unfold hylo.shape.hylo_node_tree
    simp only [hylo.sort.Pivot.Insts.HyloShapeNodeTreePlanTVec,
      hylo.sort.Concat.Insts.HyloShapeNodeTreeAlgebraTVec]
    rcases List.eq_nil_or_concat v.val with hv | ⟨v', p, hv⟩
    · apply WP.spec_bind (unfold_spec_nil inst plan v hv)
      rintro ⟨o, plan1⟩ ho
      replace ho : o = none := ho
      subst ho
      try dsimp only
      apply WP.spec_bind (fold_spec_none alg)
      rintro ⟨t, alg1⟩ ht
      replace ht : t.val = [] := ht
      show WP.spec (ok (t, plan1, alg1)) _
      rw [WP.spec_ok]
      show t.val = _
      rw [ht, hv, quicksortBy, List.reverse_nil, qsBy_nil]
    · cases n with
      | zero =>
        exfalso
        rw [hv, List.length_append, List.length_singleton] at hn
        omega
      | succ m =>
        have hlen : v'.length ≤ m := by
          rw [hv, List.length_append, List.length_singleton] at hn
          omega
        apply WP.spec_bind (unfold_spec_cons inst R hO plan v v' p hv)
        rintro ⟨o, plan1⟩ ho
        obtain ⟨l, r, hol, hl, hr⟩ := ho
        replace hol : o = some (p, l, r) := hol
        subst hol
        try dsimp only
        have hll : l.val.length ≤ m := by
          rw [hl]
          exact (List.length_filter_le _ _).trans (by rw [List.length_reverse]; exact hlen)
        have hrl : r.val.length ≤ m := by
          rw [hr]
          exact (List.length_filter_le _ _).trans (by rw [List.length_reverse]; exact hlen)
        apply WP.spec_bind (hylo_spec inst R hO m l plan1 alg hll)
        rintro ⟨l1, plan2, alg1⟩ hl1
        replace hl1 : l1.val = quicksortBy R l.val := hl1
        try dsimp only
        apply WP.spec_bind (hylo_spec inst R hO m r plan2 alg1 hrl)
        rintro ⟨r1, plan3, alg2⟩ hr1
        replace hr1 : r1.val = quicksortBy R r.val := hr1
        try dsimp only
        have hsum : l1.val.length + 1 + r1.val.length ≤ Usize.max := by
          have hvb := v.property
          rw [hv, List.length_append, List.length_singleton] at hvb
          rw [hl1, hr1, quicksortBy_length, quicksortBy_length, hl, hr]
          have h := List.length_filter_le (fun x => decide (R x < R p)) v'.reverse
          have h' := List.length_filter_le (fun x => !decide (R x < R p)) v'.reverse
          have hperm := (List.filter_append_perm (fun x => decide (R x < R p)) v'.reverse).length_eq
          rw [List.length_append, List.length_reverse] at hperm
          omega
        apply WP.spec_bind (fold_spec_some alg2 p l1 r1 hsum)
        rintro ⟨t1, alg3⟩ ht1
        replace ht1 : t1.val = l1.val ++ p :: r1.val := ht1
        show WP.spec (ok (t1, plan3, alg3)) _
        rw [WP.spec_ok]
        show t1.val = _
        rw [ht1, hl1, hr1, hl, hr, hv, quicksortBy, quicksortBy, quicksortBy, List.reverse_append,
          List.reverse_singleton, List.singleton_append, qsBy_cons]

/-- `hylo::sort::quicksort` computes `quicksortBy R`. -/
theorem quicksort_spec (inst : core.cmp.Ord T) (R : T → α) (hO : OrdSpec inst R)
    (v : alloc.vec.Vec T) :
    hylo.sort.quicksort inst v ⦃ (res : alloc.vec.Vec T) => res.val = quicksortBy R v.val ⦄ := by
  unfold hylo.sort.quicksort
  apply WP.spec_bind (hylo_spec inst R hO v.val.length v () () le_rfl)
  rintro ⟨v1, plan, alg⟩ hv1
  replace hv1 : v1.val = quicksortBy R v.val := hv1
  try dsimp only
  rw [WP.spec_ok]
  exact hv1

/-- `hylo::sort::quicksort` sorts: the output is a permutation of the input and its readings
    are sorted. -/
theorem quicksort_sound (inst : core.cmp.Ord T) (R : T → α) (hO : OrdSpec inst R)
    (v : alloc.vec.Vec T) :
    hylo.sort.quicksort inst v ⦃ (res : alloc.vec.Vec T) =>
      res.val.Perm v.val ∧ (res.val.map R).Pairwise (· ≤ ·) ⦄ := by
  apply WP.spec_mono (quicksort_spec inst R hO v)
  intro res hres
  rw [hres]
  refine ⟨?_, ?_⟩
  · exact (quicksortBy_perm R v.val)
  · rw [← quicksortBy_map]
    exact quicksort_sorted _

/-- `u64` is read by its value. -/
theorem ordSpec_u64 : OrdSpec core.cmp.OrdU64 (fun x : U64 => x.val) := by
  intro x y
  show WP.spec (ok (core.cmp.impls.PartialOrdU64.lt x y)) _
  rw [WP.spec_ok]
  show decide (x.val < y.val) = decide (x.val < y.val)
  rfl

/-- Quicksort on `u64`: a sorted permutation. -/
theorem quicksort_u64_sound (v : alloc.vec.Vec U64) :
    hylo.sort.quicksort core.cmp.OrdU64 v ⦃ (res : alloc.vec.Vec U64) =>
      res.val.Perm v.val ∧ (res.val.map fun x => x.val).Pairwise (· ≤ ·) ⦄ :=
  quicksort_sound core.cmp.OrdU64 (fun x : U64 => x.val) ordSpec_u64 v

end Formalism.RefineSort
