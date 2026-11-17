import FormalismVerify.Bits
import FormalismVerify.RefineRun

/-!
# The Rust `Bits` instance meets the model

`formalism::instances::bits::Bits` counts ones in a `u64` with wrapping addition. Read through
the representation `R` (operations by `opOf`, traces by `U64.val`), it is the model instance
`Bits.inst (Bits.modular U64.size)`: the ones counted modulo `2^64`, accepted when the count is
`k`. `tracedSpec` discharges `TracedSpec` for it, and `solve_bits_sound` is Claim 1 for the
extracted `hylo::dp::solve_bits`.
-/

namespace Formalism.BitsRust
open Aeneas Aeneas.Std Result hylo Formalism.Refine

/-- The extracted `Traced` implementation. -/
abbrev inst := formalism.instances.bits.Bits.Insts.FormalismSchemeTracedOpU64

/-- Operations, read back. -/
def opOf : formalism.instances.bits.Op → Bits.Op
  | .Leaf v => .leaf v.val
  | .Node => .node

/-- The representation: `opOf` on operations, `U64.val` on traces. -/
def R : Repr formalism.instances.bits.Op U64 Bits.Op Bits.Tau :=
  ⟨opOf, fun t => t.val, fun a b h => UScalar.val_eq_imp a b h⟩

/-- The model instance the Rust computes: ones modulo `2^64`, accepted when equal to `k`. -/
def model (p : formalism.instances.bits.Bits) : Instance Bits.Op Bits.Tau :=
  Bits.inst (Bits.modular U64.size) fun t => decide (t = p.k.val)

theorem new_val (α : Type) : (alloc.vec.Vec.new α).val = [] := rfl

/-- The sum loop, from any index: the wrapping sum of the rest, modulo `2^64`. -/
theorem sum_loop_spec (s : Slice U64) (acc : U64) (i : Usize) (hi : i.val ≤ s.length) :
    formalism.instances.bits.sum_loop s acc i ⦃ (r : U64) =>
      r.val = (acc.val + ((s.val.drop i.val).map fun t => t.val).sum) % U64.size ⦄ := by
  unfold formalism.instances.bits.sum_loop
  apply loop.spec_decr_nat (measure := fun st => s.length - st.2.val)
    (inv := fun st => st.2.val ≤ s.length ∧
      (st.1.val + ((s.val.drop st.2.val).map fun t => t.val).sum) % U64.size =
        (acc.val + ((s.val.drop i.val).map fun t => t.val).sum) % U64.size)
  · rintro ⟨acc1, i1⟩ ⟨hi1, hinv⟩
    replace hi1 : i1.val ≤ s.length := hi1
    replace hinv : (acc1.val + ((s.val.drop i1.val).map fun t => t.val).sum) % U64.size =
      (acc.val + ((s.val.drop i.val).map fun t => t.val).sum) % U64.size := hinv
    show formalism.instances.bits.sum_loop.body s acc1 i1 ⦃ _ ⦄
    unfold formalism.instances.bits.sum_loop.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : i1.val < s.val.length := by scalar_tac
      apply WP.spec_bind (Slice.index_usize_spec s i1 hlt')
      intro x hx
      replace hx : x = s.val[i1.val] := hx
      try unfold lift
      apply WP.spec_bind ((WP.spec_ok (p := fun r => r = core.num.U64.wrapping_add acc1 x) _).mpr rfl)
      intro y hy
      apply WP.spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
      intro i2 hi2
      replace hi2 : i2.val = i1.val + (1#usize).val := hi2
      have hi2' : i2.val = i1.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      rw [hy, core.num.U64.wrapping_add_val_eq, hx, UScalar.size_UScalarTyU64, hi2',
        Nat.mod_add_mod, Nat.add_assoc, ← List.sum_cons, ← List.map_cons,
        ← List.drop_eq_getElem_cons hlt']
      exact hinv
    · rename_i hge
      have hin : i1.val = s.val.length := by scalar_tac
      simp only [WP.spec_ok]
      rw [← hinv, hin, List.drop_length, List.map_nil, List.sum_nil, Nat.add_zero]
      exact (Nat.mod_eq_of_lt (by rw [U64.size_def, U64.numBits_def]; exact UScalar.hBounds acc1)).symm
  · exact ⟨hi, rfl⟩

/-- The sum of the child traces, modulo `2^64`. -/
theorem sum_spec (s : Slice U64) :
    formalism.instances.bits.sum s ⦃ (r : U64) =>
      r.val = (s.val.map fun t => t.val).sum % U64.size ⦄ := by
  unfold formalism.instances.bits.sum
  apply WP.spec_mono (sum_loop_spec s 0#u64 0#usize (by scalar_tac))
  intro r hr
  rw [hr]
  simp

theorem step_spec (p : formalism.instances.bits.Bits) (op : formalism.instances.bits.Op)
    (s : Slice U64) :
    inst.step p op s ⦃ (outs : alloc.vec.Vec (U64 × alloc.vec.Vec (U32 × U32))) =>
      outs.val.map (fun o => (R.tauOf o.1, ofPairs o.2.val)) =
        (model p).step (R.opOf op) (s.val.map R.tauOf) ⦄ := by
  show formalism.instances.bits.Bits.Insts.FormalismSchemeTracedOpU64.step p op s ⦃ _ ⦄
  unfold formalism.instances.bits.Bits.Insts.FormalismSchemeTracedOpU64.step
  apply WP.spec_bind (sum_spec s)
  intro t ht
  replace ht : t.val = (s.val.map fun t => t.val).sum % U64.size := ht
  have hnew : ∀ α : Type, (alloc.vec.Vec.new α).val.length < Usize.max := by
    intro α
    rw [new_val]
    scalar_tac
  cases op with
  | Leaf v =>
    apply WP.spec_bind (alloc.vec.Vec.push_spec (alloc.vec.Vec.new _) (v, 0#u32) (hnew _))
    intro zero hzero
    replace hzero : zero.val = [(v, 0#u32)] := by rw [hzero, new_val]; rfl
    apply WP.spec_bind (alloc.vec.Vec.push_spec (alloc.vec.Vec.new _) (t, zero) (hnew _))
    intro out hout
    replace hout : out.val = [(t, zero)] := by rw [hout, new_val]; rfl
    apply WP.spec_bind (alloc.vec.Vec.push_spec (alloc.vec.Vec.new _) (v, 1#u32) (hnew _))
    intro one hone
    replace hone : one.val = [(v, 1#u32)] := by rw [hone, new_val]; rfl
    try unfold lift
    apply WP.spec_bind ((WP.spec_ok (p := fun r => r = core.num.U64.wrapping_add t 1#u64) _).mpr rfl)
    intro t1 ht1
    have hout1 : out.val.length < Usize.max := by rw [hout]; scalar_tac
    apply WP.spec_mono (alloc.vec.Vec.push_spec out (t1, one) hout1)
    intro outs houts
    rw [houts, hout, ht1]
    simp [hzero, hone, R, opOf, model, Bits.inst, Bits.step, Bits.modular, ofPairs, ht]
  | Node =>
    apply WP.spec_mono (alloc.vec.Vec.push_spec (alloc.vec.Vec.new _)
      (t, alloc.vec.Vec.new (U32 × U32)) (hnew _))
    intro outs houts
    rw [houts, new_val]
    simp [R, opOf, model, Bits.inst, Bits.step, Bits.modular, ofPairs, ht]

theorem accept_spec (p : formalism.instances.bits.Bits) (t : U64) :
    inst.accept p t ⦃ (b : Bool) => b = (model p).accept (R.tauOf t) ⦄ := by
  show formalism.instances.bits.Bits.Insts.FormalismSchemeTracedOpU64.accept p t ⦃ _ ⦄
  unfold formalism.instances.bits.Bits.Insts.FormalismSchemeTracedOpU64.accept
  rw [WP.spec_ok]
  show decide (t = p.k) = decide (t.val = p.k.val)
  rw [decide_eq_decide]
  exact UScalar.eq_equiv t p.k

theorem eq_spec : EqSpec (inst.corecmpPartialEqInst) := by
  intro a b
  show WP.spec (ok (decide (a = b))) _
  rw [WP.spec_ok]
  exact decide_eq_true_iff

theorem clone_spec (a : U64) : inst.corecloneCloneInst.clone a ⦃ (r : U64) => r = a ⦄ := by
  show WP.spec (ok a) _
  rw [WP.spec_ok]

/-- The Rust `Bits` computes `model p`. -/
theorem tracedSpec (p : formalism.instances.bits.Bits) :
    TracedSpec R inst p (model p).toTraced :=
  ⟨eq_spec, clone_spec, step_spec p, accept_spec p⟩

theorem sizeOf_toList_le {α : Type} [SizeOf α] : ∀ {n : ℕ} (l : Data.ListN.ListN α n),
    sizeOf l.toList ≤ sizeOf l
  | _, .nil => by
    simp only [Data.ListN.ListN.toList, List.nil.sizeOf_spec, Data.ListN.ListN.nil.sizeOf_spec]
    all_goals omega
  | _, .cons a l' => by
    have ih := sizeOf_toList_le l'
    simp only [Data.ListN.ListN.toList, List.cons.sizeOf_spec, Data.ListN.ListN.cons.sizeOf_spec]
    all_goals omega

/-- A vector's list is smaller than the vector (for recursion through `Vec`-nested trees). -/
theorem sizeOf_val_lt {T : Type} [SizeOf T] (v : alloc.vec.Vec T) : sizeOf v.val < sizeOf v := by
  rcases v with ⟨⟨n, l, hb⟩⟩
  show sizeOf l.toList < sizeOf (alloc.vec.Vec.mk ⟨n, l, hb⟩)
  have := sizeOf_toList_le l
  simp only [alloc.vec.Vec.mk.sizeOf_spec, Slice.mk.sizeOf_spec]
  omega

mutual
/-- The extracted construction, read as the model's. -/
def toModel : formalism.scheme.Node formalism.instances.bits.Op → Node Bits.Op
  | .mk op cs => .mk (opOf op) (toModelList cs.val)
termination_by n => sizeOf n
decreasing_by
  all_goals
    have h := sizeOf_val_lt cs
    simp_wf
    all_goals try simp only [formalism.scheme.Node.mk.sizeOf_spec] at *
    all_goals omega
def toModelList : List (formalism.scheme.Node formalism.instances.bits.Op) → List (Node Bits.Op)
  | [] => []
  | c :: cs => toModel c :: toModelList cs
termination_by l => sizeOf l
decreasing_by
  all_goals
    simp_wf
    all_goals try simp only [List.cons.sizeOf_spec] at *
    all_goals omega
end

mutual
theorem nodeRel_toModel : ∀ n : formalism.scheme.Node formalism.instances.bits.Op,
    NodeRel R n (toModel n)
  | .mk op cs => by
    rw [toModel, NodeRel]
    exact ⟨rfl, nodeRelList_toModelList cs.val⟩
termination_by n => sizeOf n
decreasing_by
  all_goals
    have h := sizeOf_val_lt cs
    simp_wf
    all_goals try simp only [formalism.scheme.Node.mk.sizeOf_spec] at *
    all_goals omega
theorem nodeRelList_toModelList :
    ∀ cs : List (formalism.scheme.Node formalism.instances.bits.Op),
      NodeRelList R cs (toModelList cs)
  | [] => by
    rw [toModelList, NodeRelList]
    trivial
  | c :: cs => by
    rw [toModelList, NodeRelList]
    exact ⟨nodeRel_toModel c, nodeRelList_toModelList cs⟩
termination_by l => sizeOf l
decreasing_by
  all_goals
    simp_wf
    all_goals try simp only [List.cons.sizeOf_spec] at *
    all_goals omega
end

/-- Claim 1 for the extracted `hylo::dp::solve_bits`: the expression denotes exactly the
    assignments of the leaves whose number of ones is `k` modulo `2^64`. -/
theorem solve_bits_sound (p : formalism.instances.bits.Bits) (m : Node Bits.Op)
    (root : formalism.scheme.Node formalism.instances.bits.Op) (hrel : NodeRel R root m)
    (hfit : Fits (model p).toTraced m) (hwf : Bits.WF m) :
    hylo.dp.solve_bits p root ⦃ (e : formalism.expr.Expr) =>
      Sem (ofExt e) ((Bits.cands m).filter fun f => Bits.ones f % U64.size = p.k.val) ⦄ := by
  unfold hylo.dp.solve_bits
  apply WP.spec_mono (solve_sound_extracted R inst p (model p) (tracedSpec p) m root hrel hfit hwf)
  intro e he
  have heq : ((model p).candidates m).filter
      (fun f => (model p).accept ((model p).trace m f) = true) =
      (Bits.cands m).filter fun f => Bits.ones f % U64.size = p.k.val := by
    apply Finset.filter_congr
    intro f _
    simp [model, Bits.inst, Bits.modular]
  rw [heq] at he
  exact he

/-- The same, for any extracted construction: its model is `toModel root`. -/
theorem solve_bits_sound' (p : formalism.instances.bits.Bits)
    (root : formalism.scheme.Node formalism.instances.bits.Op)
    (hfit : Fits (model p).toTraced (toModel root)) (hwf : Bits.WF (toModel root)) :
    hylo.dp.solve_bits p root ⦃ (e : formalism.expr.Expr) =>
      Sem (ofExt e) ((Bits.cands (toModel root)).filter fun f =>
        Bits.ones f % U64.size = p.k.val) ⦄ :=
  solve_bits_sound p (toModel root) root (nodeRel_toModel root) hfit hwf

end Formalism.BitsRust
