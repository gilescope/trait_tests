import FormalismVerify.Spec
import FormalismVerify.Refine

/-!
# The extracted semirings compute the model's

`semiring.rs` read back: `Nat` (wrapping `u64`) is `ZMod (2^64)`, and the generic `Delta` is
the model's Δ-product (Theorem 3) for any extracted dioid `D'` and semiring `A'` that compute
model instances `D`, `A` through representations `rd`, `ra` (`DioidSpec`, `SemiringSpec`).
`Delta::new` establishes the Δ-set invariant, `Delta::add` keeps the `D`-minimum and the count
of the argmin, summing on ties: exactly `Delta.add`. `expr::eval` computes the model's `eval`
for any such semiring and measure, so by Lemma 1 it computes the measure of the expression's
semantics (`eval_measure_spec`); with `Ones` over `Nat` that is the number of solutions modulo
`2^64` (`eval_ones_card`).
-/

namespace Formalism.RefineSemiring
open Aeneas Aeneas.Std Result hylo

/-! ## `Nat`: wrapping `u64` is `ZMod (2^64)` -/

/-- The value of a `u64`, in `ZMod (2^64)`. -/
def natOf (x : U64) : ZMod (2^64) := (x.val : ZMod (2^64))

theorem val_lt (x : U64) : x.val < 2^64 := by
  have := UScalar.hBounds x
  simpa using this

theorem size_eq : UScalar.size .U64 = 2^64 := by
  rw [UScalar.size_UScalarTyU64, U64.size_def, U64.numBits_def]
  simp

theorem nat_add_spec (x y : U64) :
    formalism.semiring.Nat.Insts.FormalismSemiringSemiring.add x y
      ⦃ (r : U64) => natOf r = natOf x + natOf y ⦄ := by
  unfold formalism.semiring.Nat.Insts.FormalismSemiringSemiring.add
  try unfold lift
  apply WP.spec_bind ((WP.spec_ok (p := fun r => r = core.num.U64.wrapping_add x y) _).mpr rfl)
  intro i hi
  subst hi
  rw [WP.spec_ok]
  unfold natOf
  rw [core.num.U64.wrapping_add_val_eq, size_eq, ZMod.natCast_mod, Nat.cast_add]

theorem nat_mul_spec (x y : U64) :
    formalism.semiring.Nat.Insts.FormalismSemiringSemiring.mul x y
      ⦃ (r : U64) => natOf r = natOf x * natOf y ⦄ := by
  unfold formalism.semiring.Nat.Insts.FormalismSemiringSemiring.mul
  try unfold lift
  apply WP.spec_bind ((WP.spec_ok (p := fun r => r = core.num.U64.wrapping_mul x y) _).mpr rfl)
  intro i hi
  subst hi
  rw [WP.spec_ok]
  unfold natOf
  rw [core.num.U64.wrapping_mul_val_eq, size_eq, ZMod.natCast_mod, Nat.cast_mul]

theorem nat_zero_spec :
    formalism.semiring.Nat.Insts.FormalismSemiringSemiring.zero ⦃ (r : U64) => natOf r = 0 ⦄ := by
  unfold formalism.semiring.Nat.Insts.FormalismSemiringSemiring.zero
  rw [WP.spec_ok]
  simp [natOf]

theorem nat_one_spec :
    formalism.semiring.Nat.Insts.FormalismSemiringSemiring.one ⦃ (r : U64) => natOf r = 1 ⦄ := by
  unfold formalism.semiring.Nat.Insts.FormalismSemiringSemiring.one
  rw [WP.spec_ok]
  simp [natOf]

theorem nat_eq_spec (x y : U64) :
    formalism.semiring.Nat.Insts.CoreCmpPartialEqNat.eq x y
      ⦃ (b : Bool) => b = true ↔ natOf x = natOf y ⦄ := by
  unfold formalism.semiring.Nat.Insts.CoreCmpPartialEqNat.eq
  rw [WP.spec_ok]
  show decide (x = y) = true ↔ natOf x = natOf y
  unfold natOf
  rw [decide_eq_true_iff, UScalar.eq_equiv, ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt (val_lt x), Nat.mod_eq_of_lt (val_lt y)]

/-! ## `Delta`, generically -/

section Delta
variable {D' A' D A : Type} [Dioid D] [CommSemiring A]

/-- An extracted `Semiring` computes `A` through `ra`; its `PartialEq` decides equality of the
    values read back. -/
structure SemiringSpec (inst : formalism.semiring.Semiring A') (ra : A' → A) : Prop where
  zero : inst.zero ⦃ (r : A') => ra r = 0 ⦄
  one : inst.one ⦃ (r : A') => ra r = 1 ⦄
  add : ∀ x y : A', inst.add x y ⦃ (r : A') => ra r = ra x + ra y ⦄
  mul : ∀ x y : A', inst.mul x y ⦃ (r : A') => ra r = ra x * ra y ⦄
  eq : ∀ x y : A', inst.corecmpPartialEqInst.eq x y ⦃ (b : Bool) => b = true ↔ ra x = ra y ⦄

/-- An extracted `Dioid` computes `D` through `rd`: its semiring, its order, and `regular`
    deciding the model's regularity (the law the Rust side owes). -/
structure DioidSpec (inst : formalism.semiring.Dioid D') (rd : D' → D) : Prop where
  toSemiring : SemiringSpec inst.SemiringInst rd
  le : ∀ x y : D', inst.le x y ⦃ (b : Bool) => b = true ↔ rd x ≤ rd y ⦄
  regular : ∀ x : D', inst.regular x ⦃ (b : Bool) => b = true ↔ Dioid.regular (rd x) ⦄

/-- An extracted pair reads back as a model element. -/
structure DeltaRel (rd : D' → D) (ra : A' → A) (x : formalism.semiring.Delta D' A')
    (m : Delta D A) : Prop where
  d : rd x.d = m.d
  a : ra x.a = m.a

variable {DInst : formalism.semiring.Dioid D'} {AInst : formalism.semiring.Semiring A'}
  {rd : D' → D} {ra : A' → A}

open Classical in
/-- `Delta::new` zeroes the count of an irregular cost. -/
theorem new_spec (hD : DioidSpec DInst rd) (hA : SemiringSpec AInst ra) (d : D') (a : A') :
    formalism.semiring.Delta.new DInst AInst d a ⦃ (r : formalism.semiring.Delta D' A') =>
      rd r.d = rd d ∧ ra r.a = if Dioid.regular (rd d) then ra a else 0 ⦄ := by
  unfold formalism.semiring.Delta.new
  apply WP.spec_bind (hD.regular d)
  intro b hb
  replace hb : b = true ↔ Dioid.regular (rd d) := hb
  cases b with
  | true =>
    have hreg : Dioid.regular (rd d) := hb.mp rfl
    rw [ite_eq_left rfl, WP.spec_ok]
    exact ⟨rfl, by rw [ite_eq_left hreg]⟩
  | false =>
    have hreg : ¬ Dioid.regular (rd d) := fun h => Bool.false_ne_true (hb.mpr h)
    rw [ite_eq_right Bool.false_ne_true]
    apply WP.spec_bind hA.zero
    intro t ht
    replace ht : ra t = 0 := ht
    rw [WP.spec_ok]
    exact ⟨rfl, by rw [ite_eq_right hreg]; exact ht⟩

/-- `Delta::zero` is the model's `0`. -/
theorem zero_spec (hD : DioidSpec DInst rd) (hA : SemiringSpec AInst ra) :
    formalism.semiring.Delta.Insts.FormalismSemiringSemiring.zero DInst AInst
      ⦃ (r : formalism.semiring.Delta D' A') => DeltaRel rd ra r 0 ⦄ := by
  unfold formalism.semiring.Delta.Insts.FormalismSemiringSemiring.zero
  apply WP.spec_bind hD.toSemiring.zero
  intro t ht
  replace ht : rd t = 0 := ht
  apply WP.spec_bind hA.zero
  intro t1 ht1
  replace ht1 : ra t1 = 0 := ht1
  apply WP.spec_mono (new_spec hD hA t t1)
  intro r hr
  obtain ⟨hrd, hra⟩ := hr
  refine ⟨?_, ?_⟩
  · rw [hrd, ht, Delta.zero_d]
  · rw [hra, ht1, ite_self, Delta.zero_a]

/-- `Delta::add` is the model's `+`: the `D`-minimum with the count of the argmin, counts
    summed on a tie. -/
theorem add_spec (hD : DioidSpec DInst rd) (hA : SemiringSpec AInst ra)
    (x y : formalism.semiring.Delta D' A') (mx my : Delta D A)
    (hx : DeltaRel rd ra x mx) (hy : DeltaRel rd ra y my) :
    formalism.semiring.Delta.Insts.FormalismSemiringSemiring.add DInst AInst x y
      ⦃ (r : formalism.semiring.Delta D' A') => DeltaRel rd ra r (mx + my) ⦄ := by
  obtain ⟨hxd, hxa⟩ := hx
  obtain ⟨hyd, hya⟩ := hy
  unfold formalism.semiring.Delta.Insts.FormalismSemiringSemiring.add
  apply WP.spec_bind (hD.toSemiring.eq x.d y.d)
  intro b hb
  replace hb : b = true ↔ rd x.d = rd y.d := hb
  cases b with
  | true =>
    have heq : rd x.d = rd y.d := hb.mp rfl
    have hdd : mx.d = my.d := by rw [← hxd, ← hyd, heq]
    rw [ite_eq_left rfl]
    apply WP.spec_bind (hA.add x.a y.a)
    intro t ht
    replace ht : ra t = ra x.a + ra y.a := ht
    apply WP.spec_mono (new_spec hD hA x.d t)
    intro r hr
    obtain ⟨hrd, hra⟩ := hr
    refine ⟨?_, ?_⟩
    · rw [Delta.add_d, hrd, hxd, ← hdd, min_self]
    · rw [Delta.add_a, ← hdd, Delta.addA_self, hra]
      by_cases hreg : Dioid.regular (rd x.d)
      · rw [ite_eq_left hreg, ht, hxa, hya]
      · rw [ite_eq_right hreg]
        have h1 : mx.a = 0 := mx.inv.resolve_left (by rw [← hxd]; exact hreg)
        have h2 : my.a = 0 := my.inv.resolve_left (by rw [← hyd, ← heq]; exact hreg)
        rw [h1, h2, add_zero]
  | false =>
    have hne : rd x.d ≠ rd y.d := fun h => Bool.false_ne_true (hb.mpr h)
    rw [ite_eq_right Bool.false_ne_true]
    apply WP.spec_bind (hD.le x.d y.d)
    intro b1 hb1
    replace hb1 : b1 = true ↔ rd x.d ≤ rd y.d := hb1
    cases b1 with
    | true =>
      have hle : rd x.d ≤ rd y.d := hb1.mp rfl
      have hlt : mx.d < my.d := by rw [← hxd, ← hyd]; exact lt_of_le_of_ne hle hne
      rw [ite_eq_left rfl, WP.spec_ok]
      refine ⟨?_, ?_⟩
      · rw [Delta.add_d, min_eq_left hlt.le, hxd]
      · rw [Delta.add_a, Delta.addA_of_lt hlt, hxa]
    | false =>
      have hnle : ¬ rd x.d ≤ rd y.d := fun h => Bool.false_ne_true (hb1.mpr h)
      have hlt : my.d < mx.d := by rw [← hxd, ← hyd]; exact not_le.mp hnle
      rw [ite_eq_right Bool.false_ne_true, WP.spec_ok]
      refine ⟨?_, ?_⟩
      · rw [Delta.add_d, min_eq_right hlt.le, hyd]
      · rw [Delta.add_a, Delta.addA_of_gt hlt, hya]

/-- `Delta::one` is the model's `1`. -/
theorem one_spec (hD : DioidSpec DInst rd) (hA : SemiringSpec AInst ra) :
    formalism.semiring.Delta.Insts.FormalismSemiringSemiring.one DInst AInst
      ⦃ (r : formalism.semiring.Delta D' A') => DeltaRel rd ra r 1 ⦄ := by
  unfold formalism.semiring.Delta.Insts.FormalismSemiringSemiring.one
  apply WP.spec_bind hD.toSemiring.one
  intro t ht
  replace ht : rd t = 1 := ht
  apply WP.spec_bind hA.one
  intro t1 ht1
  replace ht1 : ra t1 = 1 := ht1
  apply WP.spec_mono (new_spec hD hA t t1)
  intro r hr
  obtain ⟨hrd, hra⟩ := hr
  refine ⟨?_, ?_⟩
  · rw [hrd, ht, Delta.one_d]
  · rw [hra, ht, ite_eq_left Dioid.regular_one, ht1, Delta.one_a]

/-- `Delta::mul` is the model's `*`: componentwise, the count zeroed when the cost turns
    irregular. -/
theorem mul_spec (hD : DioidSpec DInst rd) (hA : SemiringSpec AInst ra)
    (x y : formalism.semiring.Delta D' A') (mx my : Delta D A)
    (hx : DeltaRel rd ra x mx) (hy : DeltaRel rd ra y my) :
    formalism.semiring.Delta.Insts.FormalismSemiringSemiring.mul DInst AInst x y
      ⦃ (r : formalism.semiring.Delta D' A') => DeltaRel rd ra r (mx * my) ⦄ := by
  obtain ⟨hxd, hxa⟩ := hx
  obtain ⟨hyd, hya⟩ := hy
  unfold formalism.semiring.Delta.Insts.FormalismSemiringSemiring.mul
  apply WP.spec_bind (hD.toSemiring.mul x.d y.d)
  intro t ht
  replace ht : rd t = rd x.d * rd y.d := ht
  apply WP.spec_bind (hA.mul x.a y.a)
  intro t1 ht1
  replace ht1 : ra t1 = ra x.a * ra y.a := ht1
  apply WP.spec_mono (new_spec hD hA t t1)
  intro r hr
  obtain ⟨hrd, hra⟩ := hr
  refine ⟨?_, ?_⟩
  · rw [Delta.mul_d, hrd, ht, hxd, hyd]
  · rw [Delta.mul_a, hra]
    by_cases hreg : Dioid.regular (rd t)
    · rw [ite_eq_left hreg, ht1, hxa, hya]
    · rw [ite_eq_right hreg]
      by_cases hx : Dioid.regular mx.d
      · have hy : ¬ Dioid.regular my.d := fun hy =>
          hreg (by rw [ht, hxd, hyd]; exact Dioid.regular_mul hx hy)
        rw [my.inv.resolve_left hy, mul_zero]
      · rw [mx.inv.resolve_left hx, zero_mul]

end Delta

/-! ## `Nat` is a `SemiringSpec` -/

theorem natSpec : SemiringSpec formalism.semiring.Nat.Insts.FormalismSemiringSemiring natOf :=
  ⟨nat_zero_spec, nat_one_spec, nat_add_spec, nat_mul_spec, nat_eq_spec⟩

/-! ## `eval`: Lemma 1 for the Rust -/

section Eval
variable {A' A M' : Type} [CommSemiring A]

/-- An extracted measure computes `M` through `ra`. -/
structure MeasureSpec (inst : formalism.expr.Measure M' A') (ra : A' → A) (m : M')
    (M : Var → Val → A) : Prop where
  weight : ∀ s t : U32, inst.weight m s t ⦃ (r : A') => ra r = M s.val t.val ⦄

variable {AInst : formalism.semiring.Semiring A'} {ra : A' → A}
  {MInst : formalism.expr.Measure M' A'} {m : M'} {M : Var → Val → A}

/-- `expr::eval` computes the model's `eval`. -/
theorem eval_spec (hA : SemiringSpec AInst ra) (hM : MeasureSpec MInst ra m M) :
    ∀ e : formalism.expr.Expr,
      formalism.expr.eval AInst MInst e m ⦃ (r : A') => ra r = Formalism.eval M (Refine.ofExt e) ⦄
  | .Empty => by
    unfold formalism.expr.eval
    apply WP.spec_mono hA.zero
    intro r hr
    rw [hr, Refine.ofExt, Formalism.eval]
  | .Unit => by
    unfold formalism.expr.eval
    apply WP.spec_mono hA.one
    intro r hr
    rw [hr, Refine.ofExt, Formalism.eval]
  | .Leaf s t => by
    unfold formalism.expr.eval
    apply WP.spec_mono (hM.weight s t)
    intro r hr
    rw [hr, Refine.ofExt, Formalism.eval]
  | .Union a b => by
    unfold formalism.expr.eval
    apply WP.spec_bind (eval_spec hA hM a)
    intro t ht
    replace ht : ra t = Formalism.eval M (Refine.ofExt a) := ht
    apply WP.spec_bind (eval_spec hA hM b)
    intro t1 ht1
    replace ht1 : ra t1 = Formalism.eval M (Refine.ofExt b) := ht1
    apply WP.spec_mono (hA.add t t1)
    intro r hr
    replace hr : ra r = ra t + ra t1 := hr
    rw [hr, ht, ht1, Refine.ofExt, Formalism.eval]
  | .Join a b => by
    unfold formalism.expr.eval
    apply WP.spec_bind (eval_spec hA hM a)
    intro t ht
    replace ht : ra t = Formalism.eval M (Refine.ofExt a) := ht
    apply WP.spec_bind (eval_spec hA hM b)
    intro t1 ht1
    replace ht1 : ra t1 = Formalism.eval M (Refine.ofExt b) := ht1
    apply WP.spec_mono (hA.mul t t1)
    intro r hr
    replace hr : ra r = ra t * ra t1 := hr
    rw [hr, ht, ht1, Refine.ofExt, Formalism.eval]

/-- Lemma 1 for the Rust: on an expression denoting `F`, `eval` computes the measure of `F`. -/
theorem eval_measure_spec (hA : SemiringSpec AInst ra) (hM : MeasureSpec MInst ra m M)
    (e : formalism.expr.Expr) (F : Finset Assign) (h : Sem (Refine.ofExt e) F) :
    formalism.expr.eval AInst MInst e m ⦃ (r : A') => ra r = Formalism.measure M F ⦄ := by
  apply WP.spec_mono (eval_spec hA hM e)
  intro r hr
  rw [hr, Formalism.eval_eq_measure M h]

/-- The `Ones` measure weighs every leaf `1`. -/
theorem onesSpec (hA : SemiringSpec AInst ra) :
    MeasureSpec (formalism.expr.Ones.Insts.FormalismExprMeasure AInst) ra () (fun _ _ => 1) :=
  ⟨fun s t => by
    show AInst.one ⦃ (r : A') => ra r = 1 ⦄
    exact hA.one⟩

/-- `hylo::dp::eval_ones` over `Nat`, on an expression denoting `F`: the number of solutions
    modulo `2^64`. -/
theorem eval_ones_card (e : formalism.expr.Expr) (F : Finset Assign)
    (h : Sem (Refine.ofExt e) F) :
    hylo.dp.eval_ones formalism.semiring.Nat.Insts.FormalismSemiringSemiring e
      ⦃ (r : U64) => natOf r = (F.card : ZMod (2^64)) ⦄ := by
  unfold hylo.dp.eval_ones
  apply WP.spec_mono (eval_measure_spec natSpec (onesSpec natSpec) e F h)
  intro r hr
  rw [hr, Formalism.measure]
  simp

end Eval

end Formalism.RefineSemiring
