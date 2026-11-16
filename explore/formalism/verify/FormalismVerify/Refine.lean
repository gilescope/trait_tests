import FormalismVerify.Spec
import FormalismVerify.Extracted.Hylo

/-!
# Refinement: the extracted `scheme.rs` computes the model

`Spec.lean` models `expr.rs` and `scheme.rs` by hand; `Extracted/Hylo.lean` is what Charon and
Aeneas produce from the Rust. This file relates the two, function by function: each extracted
function succeeds, and its result, read back into the model's types (`ofExt`, `tableOf`), is
what the model computes. Claim 1 (`solve_sound`) then speaks about the Rust.

The statements use Aeneas's `⦃ ⦄` (the function succeeds and its result satisfies the
postcondition), and the loops its `loop.spec_decr_nat`.
-/

namespace Formalism.Refine
open Aeneas Aeneas.Std Result hylo

/-! ## Expressions -/

/-- The hand-written expression an extracted one denotes: `u32` variables and values read as
    naturals. -/
def ofExt : formalism.expr.Expr → Expr
  | .Empty => .empty
  | .Unit => .unit
  | .Leaf s t => .leaf s.val t.val
  | .Union a b => .union (ofExt a) (ofExt b)
  | .Join a b => .join (ofExt a) (ofExt b)

theorem ofExt_eq_empty_iff (a : formalism.expr.Expr) : ofExt a = .empty ↔ a = .Empty := by
  cases a <;> simp [ofExt]

theorem ofExt_eq_unit_iff (a : formalism.expr.Expr) : ofExt a = .unit ↔ a = .Unit := by
  cases a <;> simp [ofExt]

/-! The model's smart constructors, equation by equation. -/

theorem union'_empty_left (b : Expr) : Expr.union' .empty b = b := by cases b <;> rfl

theorem union'_empty_right (a : Expr) : Expr.union' a .empty = a := by cases a <;> rfl

theorem union'_of_ne {a b : Expr} (ha : a ≠ .empty) (hb : b ≠ .empty) :
    Expr.union' a b = .union a b := by
  cases a <;> cases b <;> first | rfl | exact absurd rfl ha | exact absurd rfl hb

theorem join'_empty_left (b : Expr) : Expr.join' .empty b = .empty := by cases b <;> rfl

theorem join'_empty_right (a : Expr) : Expr.join' a .empty = .empty := by cases a <;> rfl

theorem join'_unit_left {b : Expr} (hb : b ≠ .empty) : Expr.join' .unit b = b := by
  cases b <;> first | rfl | exact absurd rfl hb

theorem join'_unit_right {a : Expr} (ha : a ≠ .empty) : Expr.join' a .unit = a := by
  cases a <;> first | rfl | exact absurd rfl ha

theorem join'_of_ne {a b : Expr} (ha : a ≠ .empty) (hb : b ≠ .empty) (ha' : a ≠ .unit)
    (hb' : b ≠ .unit) : Expr.join' a b = .join a b := by
  cases a <;> cases b <;>
    first | rfl | exact absurd rfl ha | exact absurd rfl hb | exact absurd rfl ha'
      | exact absurd rfl hb'

/-! The derived `PartialEq` compares discriminants first; against a nullary constructor that
    is the whole test. -/

theorem discr_Unit_ne_Empty :
    (read_discriminant formalism.expr.Expr.Unit : Isize) ≠ read_discriminant .Empty := by
  show (1#isize) ≠ 0#isize
  first | scalar_tac | decide | simp

theorem discr_Leaf_ne_Empty (s t : U32) :
    (read_discriminant (formalism.expr.Expr.Leaf s t) : Isize) ≠ read_discriminant .Empty := by
  show (2#isize) ≠ 0#isize
  first | scalar_tac | decide | simp

theorem discr_Union_ne_Empty (a b : formalism.expr.Expr) :
    (read_discriminant (formalism.expr.Expr.Union a b) : Isize) ≠ read_discriminant .Empty := by
  show (3#isize) ≠ 0#isize
  first | scalar_tac | decide | simp

theorem discr_Join_ne_Empty (a b : formalism.expr.Expr) :
    (read_discriminant (formalism.expr.Expr.Join a b) : Isize) ≠ read_discriminant .Empty := by
  show (4#isize) ≠ 0#isize
  first | scalar_tac | decide | simp

theorem discr_Empty_ne_Unit :
    (read_discriminant formalism.expr.Expr.Empty : Isize) ≠ read_discriminant .Unit := by
  show (0#isize) ≠ 1#isize
  first | scalar_tac | decide | simp

theorem discr_Leaf_ne_Unit (s t : U32) :
    (read_discriminant (formalism.expr.Expr.Leaf s t) : Isize) ≠ read_discriminant .Unit := by
  show (2#isize) ≠ 1#isize
  first | scalar_tac | decide | simp

theorem discr_Union_ne_Unit (a b : formalism.expr.Expr) :
    (read_discriminant (formalism.expr.Expr.Union a b) : Isize) ≠ read_discriminant .Unit := by
  show (3#isize) ≠ 1#isize
  first | scalar_tac | decide | simp

theorem discr_Join_ne_Unit (a b : formalism.expr.Expr) :
    (read_discriminant (formalism.expr.Expr.Join a b) : Isize) ≠ read_discriminant .Unit := by
  show (4#isize) ≠ 1#isize
  first | scalar_tac | decide | simp

/-- `expr::{PartialEq}::eq` against `Empty` decides being `Empty`. -/
theorem eq_Empty_spec (a : formalism.expr.Expr) :
    formalism.expr.Expr.Insts.CoreCmpPartialEqExpr.eq a .Empty
      ⦃ (b : Bool) => b = true ↔ a = .Empty ⦄ := by
  unfold formalism.expr.Expr.Insts.CoreCmpPartialEqExpr.eq
  cases a with
  | Empty => simp
  | Unit => simp [discr_Unit_ne_Empty]
  | Leaf s t => simp [discr_Leaf_ne_Empty]
  | Union a b => simp [discr_Union_ne_Empty]
  | Join a b => simp [discr_Join_ne_Empty]

/-- `expr::{PartialEq}::eq` against `Unit` decides being `Unit`. -/
theorem eq_Unit_spec (a : formalism.expr.Expr) :
    formalism.expr.Expr.Insts.CoreCmpPartialEqExpr.eq a .Unit
      ⦃ (b : Bool) => b = true ↔ a = .Unit ⦄ := by
  unfold formalism.expr.Expr.Insts.CoreCmpPartialEqExpr.eq
  cases a with
  | Empty => simp [discr_Empty_ne_Unit]
  | Unit => simp
  | Leaf s t => simp [discr_Leaf_ne_Unit]
  | Union a b => simp [discr_Union_ne_Unit]
  | Join a b => simp [discr_Join_ne_Unit]

/-- The derived `Clone` is the identity. -/
theorem clone_spec : ∀ a : formalism.expr.Expr,
    formalism.expr.Expr.Insts.CoreCloneClone.clone a ⦃ (r : formalism.expr.Expr) => r = a ⦄
  | .Empty => by
    unfold formalism.expr.Expr.Insts.CoreCloneClone.clone
    simp
  | .Unit => by
    unfold formalism.expr.Expr.Insts.CoreCloneClone.clone
    simp
  | .Leaf s t => by
    unfold formalism.expr.Expr.Insts.CoreCloneClone.clone
    simp [lift]
  | .Union a b => by
    unfold formalism.expr.Expr.Insts.CoreCloneClone.clone
    apply WP.spec_bind (clone_spec a)
    intro a' ha'
    replace ha' : a' = a := ha'
    subst ha'
    apply WP.spec_bind (clone_spec b)
    intro b' hb'
    replace hb' : b' = b := hb'
    subst hb'
    simp
  | .Join a b => by
    unfold formalism.expr.Expr.Insts.CoreCloneClone.clone
    apply WP.spec_bind (clone_spec a)
    intro a' ha'
    replace ha' : a' = a := ha'
    subst ha'
    apply WP.spec_bind (clone_spec b)
    intro b' hb'
    replace hb' : b' = b := hb'
    subst hb'
    simp

/-- `expr::union` computes the model's `union'`. -/
theorem union_spec (a b : formalism.expr.Expr) :
    formalism.expr.union a b
      ⦃ (r : formalism.expr.Expr) => ofExt r = Expr.union' (ofExt a) (ofExt b) ⦄ := by
  unfold formalism.expr.union
  apply WP.spec_bind (eq_Empty_spec a)
  intro b1 hb1
  replace hb1 : b1 = true ↔ a = .Empty := hb1
  split
  · rename_i h
    obtain rfl := hb1.mp h
    simp [ofExt, union'_empty_left]
  · rename_i h
    have ha : a ≠ .Empty := fun e => h (hb1.mpr e)
    apply WP.spec_bind (eq_Empty_spec b)
    intro b2 hb2
    replace hb2 : b2 = true ↔ b = .Empty := hb2
    split
    · rename_i h'
      obtain rfl := hb2.mp h'
      simp [ofExt, union'_empty_right]
    · rename_i h'
      have hb : b ≠ .Empty := fun e => h' (hb2.mpr e)
      simp only [WP.spec_ok, ofExt]
      rw [union'_of_ne ((ofExt_eq_empty_iff a).not.mpr ha) ((ofExt_eq_empty_iff b).not.mpr hb)]

/-- `expr::join` computes the model's `join'`. -/
theorem join_spec (a b : formalism.expr.Expr) :
    formalism.expr.join a b
      ⦃ (r : formalism.expr.Expr) => ofExt r = Expr.join' (ofExt a) (ofExt b) ⦄ := by
  unfold formalism.expr.join
  apply WP.spec_bind (eq_Empty_spec a)
  intro b1 hb1
  replace hb1 : b1 = true ↔ a = .Empty := hb1
  split
  · rename_i h
    obtain rfl := hb1.mp h
    simp [ofExt, join'_empty_left]
  · rename_i h
    have ha : a ≠ .Empty := fun e => h (hb1.mpr e)
    apply WP.spec_bind (eq_Empty_spec b)
    intro b2 hb2
    replace hb2 : b2 = true ↔ b = .Empty := hb2
    split
    · rename_i h'
      obtain rfl := hb2.mp h'
      simp [ofExt, join'_empty_right]
    · rename_i h'
      have hb : b ≠ .Empty := fun e => h' (hb2.mpr e)
      apply WP.spec_bind (eq_Unit_spec a)
      intro b3 hb3
      replace hb3 : b3 = true ↔ a = .Unit := hb3
      split
      · rename_i h''
        obtain rfl := hb3.mp h''
        simp only [WP.spec_ok, ofExt]
        rw [join'_unit_left ((ofExt_eq_empty_iff b).not.mpr hb)]
      · rename_i h''
        have ha' : a ≠ .Unit := fun e => h'' (hb3.mpr e)
        apply WP.spec_bind (eq_Unit_spec b)
        intro b4 hb4
        replace hb4 : b4 = true ↔ b = .Unit := hb4
        split
        · rename_i h3
          obtain rfl := hb4.mp h3
          simp only [WP.spec_ok, ofExt]
          rw [join'_unit_right ((ofExt_eq_empty_iff a).not.mpr ha)]
        · rename_i h3
          have hb' : b ≠ .Unit := fun e => h3 (hb4.mpr e)
          simp only [WP.spec_ok, ofExt]
          rw [join'_of_ne ((ofExt_eq_empty_iff a).not.mpr ha) ((ofExt_eq_empty_iff b).not.mpr hb)
            ((ofExt_eq_unit_iff a).not.mpr ha') ((ofExt_eq_unit_iff b).not.mpr hb')]

/-- Leaves, read back. -/
def ofPairs (l : List (U32 × U32)) : List (Var × Val) := l.map fun p => (p.1.val, p.2.val)

/-- The loop of `expr::join_leaves`, from any index. -/
theorem join_leaves_loop_spec (leaves : Slice (U32 × U32)) (e : formalism.expr.Expr)
    (i : Usize) (hi : i.val ≤ leaves.length) :
    formalism.expr.join_leaves_loop e leaves i ⦃ (r : formalism.expr.Expr) =>
      ofExt r = Expr.joinLeaves (ofExt e) (ofPairs (leaves.val.drop i.val)) ⦄ := by
  unfold formalism.expr.join_leaves_loop
  apply loop.spec_decr_nat (measure := fun s => leaves.length - s.2.val)
    (inv := fun s => s.2.val ≤ leaves.length ∧
      Expr.joinLeaves (ofExt s.1) (ofPairs (leaves.val.drop s.2.val)) =
        Expr.joinLeaves (ofExt e) (ofPairs (leaves.val.drop i.val)))
  · rintro ⟨e1, i1⟩ ⟨hi1, hacc⟩
    replace hi1 : i1.val ≤ leaves.length := hi1
    replace hacc : Expr.joinLeaves (ofExt e1) (ofPairs (leaves.val.drop i1.val)) =
      Expr.joinLeaves (ofExt e) (ofPairs (leaves.val.drop i.val)) := hacc
    beta_reduce
    unfold formalism.expr.join_leaves_loop.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : i1.val < leaves.length := by scalar_tac
      apply WP.spec_bind (Slice.index_usize_spec leaves i1 hlt')
      rintro ⟨i2, i3⟩ hp
      replace hp : (i2, i3) = leaves.val[i1.val] := hp
      dsimp only
      apply WP.spec_bind (join_spec e1 (.Leaf i2 i3))
      intro e2 he2
      replace he2 : ofExt e2 = Expr.join' (ofExt e1) (ofExt (.Leaf i2 i3)) := he2
      apply WP.spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
      intro i4 hi4
      replace hi4 : i4.val = i1.val + (1#usize).val := hi4
      have hi4' : i4.val = i1.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      rw [hi4', ← hacc, List.drop_eq_getElem_cons hlt', ← hp]
      simp [ofPairs, Expr.joinLeaves, he2, ofExt]
    · rename_i hge
      have hnil : leaves.val.drop i1.val = [] := List.drop_eq_nil_of_le (by scalar_tac)
      simp only [WP.spec_ok]
      rw [← hacc, hnil]
      simp [ofPairs, Expr.joinLeaves]
  · exact ⟨hi, rfl⟩

/-- `expr::join_leaves` computes the model's `joinLeaves`. -/
theorem join_leaves_spec (e : formalism.expr.Expr) (leaves : Slice (U32 × U32)) :
    formalism.expr.join_leaves e leaves ⦃ (r : formalism.expr.Expr) =>
      ofExt r = Expr.joinLeaves (ofExt e) (ofPairs leaves.val) ⦄ := by
  unfold formalism.expr.join_leaves
  have h := join_leaves_loop_spec leaves e 0#usize (by scalar_tac)
  have h0 : (0#usize).val = 0 := by scalar_tac
  rw [h0, List.drop_zero] at h
  exact h

/-! ## Tables -/

section Table
variable {Tau : Type} [DecidableEq Tau]

/-- A row, read back. -/
def rowOf (r : formalism.scheme.Row Tau) : Tau × Expr := (r.tau, ofExt r.expr)

/-- A table, read back. -/
def tableOf (t : alloc.vec.Vec (formalism.scheme.Row Tau)) : List (Tau × Expr) :=
  t.val.map rowOf

/-- `PartialEq` on traces decides equality. -/
def EqSpec (inst : core.cmp.PartialEq Tau Tau) : Prop :=
  ∀ a b : Tau, inst.eq a b ⦃ (r : Bool) => r = true ↔ a = b ⦄

theorem set_eq_take_cons_drop' {α : Type*} :
    ∀ (l : List α) (n : ℕ) (a : α), n < l.length → l.set n a = l.take n ++ a :: l.drop (n + 1)
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => by simp
  | x :: l, n + 1, a, h => by
    simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    rw [set_eq_take_cons_drop' l n a (by simpa using h)]

/-- `unionInto` leaves the rows before the first match alone. -/
theorem unionInto_prefix (tau : Tau) (e : Expr) :
    ∀ (T : List (Tau × Expr)) (i : ℕ), (∀ j, (hj : j < T.length) → j < i → (T[j]).1 ≠ tau) →
      Traced.unionInto T tau e = T.take i ++ Traced.unionInto (T.drop i) tau e
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | (t, e') :: rest, i + 1, h => by
    have hr : t ≠ tau := h 0 (by simp) (Nat.succ_pos i)
    rw [List.take_succ_cons, List.drop_succ_cons, List.cons_append, Traced.unionInto,
      ite_eq_right hr,
      unionInto_prefix tau e rest i fun j hj hji => h (j + 1) (by simpa using hj)
        (Nat.succ_lt_succ hji)]

/-- The loop of `scheme::union_into`, from any index whose predecessors do not match. -/
theorem union_into_loop_spec (inst : core.cmp.PartialEq Tau Tau) (hinst : EqSpec inst)
    (table : alloc.vec.Vec (formalism.scheme.Row Tau)) (tau : Tau) (e : formalism.expr.Expr)
    (hlen : table.length < Usize.max) (i : Usize) (hi : i.val ≤ table.length)
    (hpre : ∀ j, (hj : j < table.val.length) → j < i.val → (table.val[j]).tau ≠ tau) :
    formalism.scheme.union_into_loop inst table tau e i
      ⦃ (t : alloc.vec.Vec (formalism.scheme.Row Tau)) =>
        tableOf t = Traced.unionInto (tableOf table) tau (ofExt e) ⦄ := by
  unfold formalism.scheme.union_into_loop
  apply loop.spec_decr_nat (measure := fun k => table.length - k.val)
    (inv := fun k => k.val ≤ table.length ∧
      ∀ j, (hj : j < table.val.length) → j < k.val → (table.val[j]).tau ≠ tau)
  · intro k ⟨hk, hkpre⟩
    replace hk : k.val ≤ table.length := hk
    replace hkpre : ∀ j, (hj : j < table.val.length) → j < k.val → (table.val[j]).tau ≠ tau := hkpre
    beta_reduce
    unfold formalism.scheme.union_into_loop.body
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
    split
    · rename_i hlt
      have hlt' : k.val < table.length := by scalar_tac
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec table k hlt')
      intro r hr
      replace hr : r = table.val[k.val] := hr
      apply WP.spec_bind (hinst r.tau tau)
      intro b hb
      replace hb : b = true ↔ r.tau = tau := hb
      split
      · rename_i hbt
        have htau : r.tau = tau := hb.mp hbt
        apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec table k hlt')
        rintro ⟨r1, back⟩ hp
        have hp' : r1 = table.val[k.val] ∧ back = table.set k := hp
        obtain ⟨hr1, hback⟩ := hp'
        dsimp only
        simp only [core.mem.replace]
        apply WP.spec_bind (union_spec r1.expr e)
        intro e2 he2
        replace he2 : ofExt e2 = Expr.union' (ofExt r1.expr) (ofExt e) := he2
        subst hback
        dsimp only
        have hlt1 : k.val < (table.set k { r1 with expr := .Empty }).length := by
          simp [hlt']
        apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec _ k hlt1)
        rintro ⟨r2, back1⟩ hp
        have hp' : r2 = (table.set k { r1 with expr := .Empty }).val[k.val] ∧
            back1 = (table.set k { r1 with expr := .Empty }).set k := hp
        obtain ⟨hr2, hback1⟩ := hp'
        subst hback1
        dsimp only
        simp only [WP.spec_ok]
        -- the rows before `k` do not match, the row at `k` does
        have hpre' : ∀ j, (hj : j < (tableOf table).length) → j < k.val →
            ((tableOf table)[j]).1 ≠ tau := by
          intro j hj hjk
          simp only [tableOf, List.getElem_map, rowOf]
          exact hkpre j (by simpa [tableOf] using hj) hjk
        rw [unionInto_prefix tau (ofExt e) (tableOf table) k.val hpre']
        have hdrop : (tableOf table).drop k.val =
            (r.tau, ofExt r.expr) :: (tableOf table).drop (k.val + 1) := by
          rw [tableOf, List.drop_eq_getElem_cons (by simpa using hlt'), List.getElem_map, ← hr]
          rfl
        rw [hdrop, Traced.unionInto, ite_eq_left htau]
        -- the result: row `k` replaced
        have hr2' : r2 = { r1 with expr := .Empty } := by
          rw [hr2]
          simp [alloc.vec.Vec.set_val_eq, hlt']
        subst hr2'
        have hr1r : r1 = r := hr1.trans hr.symm
        subst hr1r
        simp only [tableOf, alloc.vec.Vec.set_val_eq, List.set_set, List.map_set]
        rw [set_eq_take_cons_drop' _ _ _ (by simpa using hlt')]
        simp [rowOf, he2]
      · rename_i hbf
        have hne : r.tau ≠ tau := fun h => hbf (hb.mpr h)
        apply WP.spec_bind (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
        intro k1 hk1
        replace hk1 : k1.val = k.val + (1#usize).val := hk1
        have hk1' : k1.val = k.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
        intro j hj hjk
        rw [hk1'] at hjk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hjk | rfl
        · exact hkpre j hj hjk
        · rw [← hr]
          exact hne
    · rename_i hge
      have hge' : table.length ≤ k.val := by scalar_tac
      apply WP.spec_bind (alloc.vec.Vec.push_spec table { tau, expr := e } hlen)
      intro t1 ht1
      replace ht1 : t1.val = table.val ++ [{ tau, expr := e }] := ht1
      simp only [WP.spec_ok]
      have hall : ∀ j, (hj : j < (tableOf table).length) → j < (tableOf table).length →
          ((tableOf table)[j]).1 ≠ tau := by
        intro j hj _
        simp only [tableOf, List.getElem_map, rowOf]
        exact hkpre j (by simpa [tableOf] using hj) (by simp [tableOf] at hj; scalar_tac)
      rw [unionInto_prefix tau (ofExt e) (tableOf table) (tableOf table).length hall,
        List.take_length, List.drop_length]
      simp [tableOf, ht1, rowOf, Traced.unionInto]
  · exact ⟨hi, hpre⟩

/-- `scheme::union_into` computes the model's `unionInto`. -/
theorem union_into_spec (inst : core.cmp.PartialEq Tau Tau) (hinst : EqSpec inst)
    (table : alloc.vec.Vec (formalism.scheme.Row Tau)) (tau : Tau) (e : formalism.expr.Expr)
    (hlen : table.length < Usize.max) :
    formalism.scheme.union_into inst table tau e
      ⦃ (t : alloc.vec.Vec (formalism.scheme.Row Tau)) =>
        tableOf t = Traced.unionInto (tableOf table) tau (ofExt e) ⦄ := by
  unfold formalism.scheme.union_into
  exact union_into_loop_spec inst hinst table tau e hlen 0#usize (by scalar_tac)
    (fun _ _ h => absurd h (by scalar_tac))

end Table

end Formalism.Refine
