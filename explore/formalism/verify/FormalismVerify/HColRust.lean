import FormalismVerify.HColList
import FormalismVerify.RefineRun
import FormalismVerify.RefineHylo

/-!
# The Rust H-colouring instance computes the model

`instances/hcol.rs`, as Aeneas extracts it, read through `R`: an operation's variable is its
value, a trace (a `Vec<(u32, u32)>` sorted by variable) is the list of its pairs' values. Its
`step` and `accept` compute the list model's (`HColList.instL`) wherever the model's `run` calls
them (`hcolOk`: the right number of children, traces that fit), so `scheme::solve` on it
denotes exactly the `H`-colourings (`solve_hcol_sound`).
-/

namespace Formalism.HColRust
open Aeneas Aeneas.Std Result hylo Formalism Formalism.Refine Formalism.HCol

abbrev inst := formalism.instances.hcol.HColoring.Insts.FormalismSchemeTracedOpTau

/-! ## Small tools for following the extracted code -/

theorem spec_bind_ok {α β : Type} {x : α} {k : α → Result β} {P : β → Prop}
    (h : WP.spec (k x) P) : WP.spec (Std.bind (ok x) k) P :=
  WP.spec_bind ((WP.spec_ok (p := fun r => r = x) x).mpr rfl) fun y hy => by
    rw [show y = x from hy]
    exact h

theorem spec_ite {α : Type} {c : Prop} [Decidable c] {m1 m2 : Result α} {P : α → Prop}
    (h1 : c → WP.spec m1 P) (h2 : ¬ c → WP.spec m2 P) : WP.spec (if c then m1 else m2) P := by
  split
  · exact h1 (by assumption)
  · exact h2 (by assumption)

theorem spec_bind_ite {α β : Type} {c : Prop} [Decidable c] {m1 m2 : Result α} {k : α → Result β}
    {P : β → Prop} (h1 : c → WP.spec (Std.bind m1 k) P) (h2 : ¬ c → WP.spec (Std.bind m2 k) P) :
    WP.spec (Std.bind (if c then m1 else m2) k) P := by
  split
  · exact h1 (by assumption)
  · exact h2 (by assumption)

theorem new_val (α : Type) : (alloc.vec.Vec.new α).val = [] := rfl

theorem new_len {α : Type} : (alloc.vec.Vec.new α).val.length < Usize.max := by
  rw [new_val]
  scalar_tac

theorem deref_val {α : Type} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  rw [alloc.vec.Vec.deref, Slice.from_val]

/-! ## The representation -/

/-- The model operation of an extracted one. -/
def opOf : formalism.instances.hcol.Op → HOp
  | .Leaf => .leaf
  | .Introduce v o => .intro v.val o
  | .Forget v => .forget v.val
  | .Join => .join

/-- A trace, read as the list of its pairs' values. -/
def tauOf (t : formalism.instances.hcol.Tau) : TauL := ofPairs t.val

theorem ofPairs_cons (p : U32 × U32) (l : List (U32 × U32)) :
    ofPairs (p :: l) = (p.1.val, p.2.val) :: ofPairs l := rfl

theorem ofPairs_nil : ofPairs [] = [] := rfl

theorem ofPairs_length (l : List (U32 × U32)) : (ofPairs l).length = l.length := by
  simp [ofPairs]

theorem ofPairs_injective : Function.Injective ofPairs := by
  intro l l' h
  unfold ofPairs at h
  refine List.map_injective_iff.mpr ?_ h
  intro p q hpq
  rw [Prod.mk.injEq] at hpq
  exact Prod.ext (UScalar.val_eq_imp _ _ hpq.1) (UScalar.val_eq_imp _ _ hpq.2)

theorem tauOf_injective : Function.Injective tauOf := by
  intro t t' h
  exact alloc.vec.Vec.ext _ _ (ofPairs_injective h)

def R : Repr formalism.instances.hcol.Op formalism.instances.hcol.Tau HOp TauL :=
  ⟨opOf, tauOf, tauOf_injective⟩

/-- Whether a row of the adjacency list holds the vertex `w`. -/
def adjRow (row : alloc.vec.Vec U32) (w : ℕ) : Bool := decide (∃ x ∈ row.val, x.val = w)

/-- The graphs of a Rust `HColoring`: `u` is adjacent to `w` when `w` is in `u`'s row (a vertex
    outside the graph has none); `H` has as many colours as vertices, counted in a `u32`. -/
def adjOf (g : formalism.instances.hcol.Graph) (u w : ℕ) : Bool :=
  match g.adj.val[u]? with
  | some row => adjRow row w
  | none => false

def graphsOf (p : formalism.instances.hcol.HColoring) : Graphs :=
  { adjG := adjOf p.g, adjH := adjOf p.h, nH := p.h.adj.val.length % 2 ^ 32 }

theorem graphsOf_nH (p : formalism.instances.hcol.HColoring) :
    (graphsOf p).nH = p.h.adj.val.length % 2 ^ 32 := rfl

/-- Where the Rust `step` is defined: as many children as the operation takes, traces that can
    grow by one. -/
def hcolOk (op : HOp) (taus : List TauL) : Prop :=
  (∀ t ∈ taus, t.length < Usize.max) ∧
    match op with
    | .leaf => True
    | .intro _ _ => taus ≠ []
    | .forget _ => taus ≠ []
    | .join => 2 ≤ taus.length

/-! ## `Graph::has_edge` -/

/-- Whether a list holds `v`. -/
def hasVal : List U32 → U32 → Bool
  | [], _ => false
  | x :: l, v => decide (x = v) || hasVal l v

theorem hasVal_iff (v : U32) : ∀ l : List U32, hasVal l v = true ↔ ∃ x ∈ l, x = v
  | [] => by
    rw [hasVal]
    exact ⟨fun h => nomatch h, fun ⟨_, h, _⟩ => nomatch h⟩
  | x :: l => by
    rw [hasVal, Bool.or_eq_true, decide_eq_true_iff, hasVal_iff v l]
    constructor
    · rintro (h | ⟨y, hy, rfl⟩)
      · exact ⟨x, List.mem_cons_self .., h⟩
      · exact ⟨y, List.mem_cons_of_mem _ hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Or.inl rfl
      · exact Or.inr ⟨y, hy, rfl⟩

theorem has_edge_loop_spec (v : U32) (found : Bool) (row : alloc.vec.Vec U32) (i : Usize)
    (hi : i.val ≤ row.val.length) :
    formalism.instances.hcol.Graph.has_edge_loop v found row i ⦃ (b : Bool) =>
      b = (found || hasVal (row.val.drop i.val) v) ⦄ := by
  unfold formalism.instances.hcol.Graph.has_edge_loop
  apply loop.spec_decr_nat (measure := fun (st : Bool × Usize) => row.val.length - st.2.val)
    (inv := fun (st : Bool × Usize) => st.2.val ≤ row.val.length ∧
      (st.1 || hasVal (row.val.drop st.2.val) v) = (found || hasVal (row.val.drop i.val) v))
  · rintro ⟨found1, i1⟩ ⟨hi1, hinv⟩
    replace hi1 : i1.val ≤ row.val.length := hi1
    replace hinv : (found1 || hasVal (row.val.drop i1.val) v) =
      (found || hasVal (row.val.drop i.val) v) := hinv
    show formalism.instances.hcol.Graph.has_edge_loop.body v row found1 i1 ⦃ _ ⦄
    unfold formalism.instances.hcol.Graph.has_edge_loop.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : i1.val < row.val.length := by scalar_tac
      rw [alloc.vec.Vec.index_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec row i1 hlt')
      intro x hx
      replace hx : x = row.val[i1.val] := hx
      apply spec_bind_ite
      · intro hxv
        apply spec_bind_ok
        apply WP.spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
        intro i2 hi2
        replace hi2 : i2.val = i1.val + (1#usize).val := hi2
        have hi2' : i2.val = i1.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
        rw [← hinv, hi2', List.drop_eq_getElem_cons hlt', ← hx, hasVal, decide_eq_true hxv,
          Bool.true_or, Bool.true_or, Bool.or_true]
      · intro hxv
        apply spec_bind_ok
        apply WP.spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
        intro i2 hi2
        replace hi2 : i2.val = i1.val + (1#usize).val := hi2
        have hi2' : i2.val = i1.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
        rw [← hinv, hi2', List.drop_eq_getElem_cons hlt', ← hx, hasVal, decide_eq_false hxv,
          Bool.false_or]
    · rename_i hge
      have hin : i1.val = row.val.length := by scalar_tac
      simp only [WP.spec_ok]
      rw [← hinv, hin, List.drop_length, hasVal]
  · exact ⟨hi, rfl⟩

theorem adjOf_of_lt {g : formalism.instances.hcol.Graph} {u : ℕ} (hu : u < g.adj.val.length)
    (w : ℕ) : adjOf g u w = adjRow (g.adj.val[u]) w := by
  unfold adjOf
  rw [List.getElem?_eq_getElem hu]

theorem adjOf_of_ge {g : formalism.instances.hcol.Graph} {u : ℕ} (hu : g.adj.val.length ≤ u)
    (w : ℕ) : adjOf g u w = false := by
  unfold adjOf
  rw [List.getElem?_eq_none_iff.mpr hu]

theorem hasVal_eq_adjRow (row : alloc.vec.Vec U32) (v : U32) : hasVal row.val v = adjRow row v.val := by
  rw [Bool.eq_iff_iff, hasVal_iff, adjRow, decide_eq_true_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, hxv⟩
    exact ⟨x, hx, UScalar.val_eq_imp _ _ hxv⟩

theorem has_edge_spec (g : formalism.instances.hcol.Graph) (u v : U32) :
    formalism.instances.hcol.Graph.has_edge g u v ⦃ (b : Bool) => b = adjOf g u.val v.val ⦄ := by
  unfold formalism.instances.hcol.Graph.has_edge
  apply spec_bind_ok
  try dsimp only
  apply spec_ite
  · intro hlt
    have hlt' : u.val < g.adj.val.length := by
      rw [UScalar.lt_equiv, U32.cast_Usize_val_eq, alloc.vec.Vec.len_val] at hlt
      exact hlt
    apply spec_bind_ok
    rw [alloc.vec.Vec.index_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec g.adj (UScalar.cast .Usize u)
      (by rw [U32.cast_Usize_val_eq]; exact hlt'))
    intro row hrow
    replace hrow : row = g.adj.val[(UScalar.cast .Usize u).val] := hrow
    simp only [U32.cast_Usize_val_eq] at hrow
    apply WP.spec_mono (has_edge_loop_spec v false row 0#usize (by simp))
    intro b hb
    rw [hb, adjOf_of_lt hlt', hrow, Bool.false_or]
    simp only [Usize.ofNat_val_eq, List.drop_zero]
    exact hasVal_eq_adjRow _ v
  · intro hge
    rw [WP.spec_ok]
    have hge' : g.adj.val.length ≤ u.val := by
      rw [UScalar.lt_equiv, U32.cast_Usize_val_eq, alloc.vec.Vec.len_val] at hge
      omega
    rw [adjOf_of_ge hge']

/-! ## `insert_sorted` -/

/-- `insertSorted` on the code's pairs. -/
def insertSortedU : List (U32 × U32) → U32 → U32 → List (U32 × U32)
  | [], v, d => [(v, d)]
  | p :: rest, v, d => if v.val < p.1.val then (v, d) :: p :: rest else p :: insertSortedU rest v d

theorem ofPairs_insertSortedU (v d : U32) :
    ∀ l : List (U32 × U32), ofPairs (insertSortedU l v d) = insertSorted (ofPairs l) v.val d.val
  | [] => rfl
  | p :: rest => by
    rw [insertSortedU, ofPairs_cons, insertSorted]
    by_cases h : v.val < p.1.val
    · rw [if_pos h, if_pos h, ofPairs_cons, ofPairs_cons]
    · rw [if_neg h, if_neg h, ofPairs_cons, ofPairs_insertSortedU v d rest]

theorem insertSortedU_eq_append (v d : U32) :
    ∀ l : List (U32 × U32), (∀ q ∈ l, ¬ v.val < q.1.val) → insertSortedU l v d = l ++ [(v, d)]
  | [], _ => rfl
  | p :: rest, h => by
    rw [insertSortedU, if_neg (h p (List.mem_cons_self ..)), List.cons_append,
      insertSortedU_eq_append v d rest fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem insertSortedU_eq_of_split (v d : U32) :
    ∀ (l1 : List (U32 × U32)) (p : U32 × U32) (l2 : List (U32 × U32)),
      (∀ q ∈ l1, ¬ v.val < q.1.val) → v.val < p.1.val →
      insertSortedU (l1 ++ p :: l2) v d = l1 ++ (v, d) :: p :: l2
  | [], p, l2, _, hp => by
    rw [List.nil_append, insertSortedU, if_pos hp, List.nil_append]
  | q :: l1, p, l2, h, hp => by
    rw [List.cons_append, insertSortedU, if_neg (h q (List.mem_cons_self ..)), List.cons_append,
      insertSortedU_eq_of_split v d l1 p l2 (fun r hr => h r (List.mem_cons_of_mem _ hr)) hp]

/-- The first loop: copy the pairs at or below `v`. -/
theorem insert_sorted_loop0_spec (f : Slice (U32 × U32)) (v : U32) (out : alloc.vec.Vec (U32 × U32))
    (i : Usize) (hi : i.val ≤ f.val.length) (hout : out.val = f.val.take i.val)
    (hq : ∀ q ∈ f.val.take i.val, ¬ v.val < q.1.val) :
    formalism.instances.hcol.insert_sorted_loop0 f v out i
      ⦃ (res : alloc.vec.Vec (U32 × U32) × Usize) =>
        res.2.val ≤ f.val.length ∧ res.1.val = f.val.take res.2.val ∧
        (∀ q ∈ f.val.take res.2.val, ¬ v.val < q.1.val) ∧
        ∀ h : res.2.val < f.val.length, v.val < (f.val[res.2.val]).1.val ⦄ := by
  unfold formalism.instances.hcol.insert_sorted_loop0
  apply loop.spec_decr_nat (measure := fun (st : alloc.vec.Vec (U32 × U32) × Usize) =>
      f.val.length - st.2.val)
    (inv := fun (st : alloc.vec.Vec (U32 × U32) × Usize) => st.2.val ≤ f.val.length ∧
      st.1.val = f.val.take st.2.val ∧ ∀ q ∈ f.val.take st.2.val, ¬ v.val < q.1.val)
  · rintro ⟨out1, i1⟩ ⟨hi1, hout1, hq1⟩
    replace hi1 : i1.val ≤ f.val.length := hi1
    replace hout1 : out1.val = f.val.take i1.val := hout1
    replace hq1 : ∀ q ∈ f.val.take i1.val, ¬ v.val < q.1.val := hq1
    show formalism.instances.hcol.insert_sorted_loop0.body f v out1 i1 ⦃ _ ⦄
    unfold formalism.instances.hcol.insert_sorted_loop0.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : i1.val < f.val.length := by scalar_tac
      apply WP.spec_bind (Slice.index_usize_spec f i1 hlt')
      rintro ⟨i2, c⟩ hp
      have hp' : (i2, c) = f.val[i1.val] := hp
      have hi2 : i2 = (f.val[i1.val]).1 := by rw [← hp']
      apply spec_ite
      · intro hle
        have hle' : ¬ v.val < (f.val[i1.val]).1.val := by
          rw [← hi2]
          exact Nat.not_lt.mpr ((UScalar.le_equiv i2 v).mp hle)
        apply WP.spec_bind (Slice.index_usize_spec f i1 hlt')
        intro p hp2
        replace hp2 : p = f.val[i1.val] := hp2
        have hlen1 : out1.val.length < Usize.max := by
          have := f.length_ineq
          rw [hout1, List.length_take]
          omega
        apply WP.spec_bind (alloc.vec.Vec.push_spec out1 p hlen1)
        intro out2 hout2
        replace hout2 : out2.val = out1.val ++ [p] := hout2
        apply WP.spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
        intro i3 hi3
        replace hi3 : i3.val = i1.val + (1#usize).val := hi3
        have hi3' : i3.val = i1.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
        · rw [hout2, hout1, hp2, hi3', List.take_succ_eq_append_getElem hlt']
        · intro q hq'
          rw [hi3', List.take_succ_eq_append_getElem hlt', List.mem_append, List.mem_singleton] at hq'
          rcases hq' with hq' | rfl
          · exact hq1 q hq'
          · exact hle'
      · intro hgt
        have hgt' : v.val < (f.val[i1.val]).1.val := by
          rw [← hi2]
          exact Nat.lt_of_not_le fun h => hgt ((UScalar.le_equiv i2 v).mpr h)
        rw [WP.spec_ok]
        exact ⟨hi1, hout1, hq1, fun _ => hgt'⟩
    · rename_i hge
      have hin : i1.val = f.val.length := by scalar_tac
      rw [WP.spec_ok]
      exact ⟨hi1, hout1, hq1, fun h => absurd h (by rw [hin]; exact lt_irrefl _)⟩
  · exact ⟨hi, hout, hq⟩

/-- The second loop: copy the rest. -/
theorem insert_sorted_loop1_spec (f : Slice (U32 × U32)) (out : alloc.vec.Vec (U32 × U32))
    (i : Usize) (hi : i.val ≤ f.val.length)
    (hlen : out.val.length + (f.val.length - i.val) ≤ Usize.max) :
    formalism.instances.hcol.insert_sorted_loop1 f out i
      ⦃ (res : alloc.vec.Vec (U32 × U32)) => res.val = out.val ++ f.val.drop i.val ⦄ := by
  unfold formalism.instances.hcol.insert_sorted_loop1
  apply loop.spec_decr_nat (measure := fun (st : alloc.vec.Vec (U32 × U32) × Usize) =>
      f.val.length - st.2.val)
    (inv := fun (st : alloc.vec.Vec (U32 × U32) × Usize) => st.2.val ≤ f.val.length ∧
      st.1.val ++ f.val.drop st.2.val = out.val ++ f.val.drop i.val)
  · rintro ⟨out1, i1⟩ ⟨hi1, hinv⟩
    replace hi1 : i1.val ≤ f.val.length := hi1
    replace hinv : out1.val ++ f.val.drop i1.val = out.val ++ f.val.drop i.val := hinv
    show formalism.instances.hcol.insert_sorted_loop1.body f out1 i1 ⦃ _ ⦄
    unfold formalism.instances.hcol.insert_sorted_loop1.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : i1.val < f.val.length := by scalar_tac
      apply WP.spec_bind (Slice.index_usize_spec f i1 hlt')
      intro p hp
      replace hp : p = f.val[i1.val] := hp
      have hlen1 : out1.val.length < Usize.max := by
        have := congrArg List.length hinv
        rw [List.length_append, List.length_append, List.length_drop, List.length_drop] at this
        omega
      apply WP.spec_bind (alloc.vec.Vec.push_spec out1 p hlen1)
      intro out2 hout2
      replace hout2 : out2.val = out1.val ++ [p] := hout2
      apply WP.spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
      intro i2 hi2
      replace hi2 : i2.val = i1.val + (1#usize).val := hi2
      have hi2' : i2.val = i1.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      rw [hout2, hi2', List.append_assoc, List.singleton_append, hp,
        ← List.drop_eq_getElem_cons hlt']
      exact hinv
    · rename_i hge
      have hin : i1.val = f.val.length := by scalar_tac
      rw [WP.spec_ok]
      rw [hin, List.drop_length, List.append_nil] at hinv
      exact hinv
  · exact ⟨hi, hinv⟩

theorem insert_sorted_spec (f : Slice (U32 × U32)) (v d : U32) (hlen : f.val.length < Usize.max) :
    formalism.instances.hcol.insert_sorted f v d ⦃ (res : alloc.vec.Vec (U32 × U32)) =>
      res.val = insertSortedU f.val v d ⦄ := by
  unfold formalism.instances.hcol.insert_sorted
  apply WP.spec_bind (insert_sorted_loop0_spec f v (alloc.vec.Vec.new _) 0#usize (by simp)
    (by rw [new_val]; simp) (by simp))
  rintro ⟨out, k⟩ hp
  have hp' : k.val ≤ f.val.length ∧ out.val = f.val.take k.val ∧
    (∀ q ∈ f.val.take k.val, ¬ v.val < q.1.val) ∧
    ∀ h : k.val < f.val.length, v.val < (f.val[k.val]).1.val := hp
  obtain ⟨hk, hout, hq, hgt⟩ := hp'
  have houtlen : out.val.length < Usize.max := by
    rw [hout, List.length_take]
    omega
  apply WP.spec_bind (alloc.vec.Vec.push_spec out (v, d) houtlen)
  intro out1 hout1
  replace hout1 : out1.val = out.val ++ [(v, d)] := hout1
  apply WP.spec_mono (insert_sorted_loop1_spec f out1 k hk
    (by rw [hout1, List.length_append, hout, List.length_take, List.length_singleton]; omega))
  intro res hres
  rw [hres, hout1, hout]
  rcases Nat.lt_or_ge k.val f.val.length with hlt | hge
  · have hsplit : f.val = f.val.take k.val ++ f.val[k.val] :: f.val.drop (k.val + 1) := by
      rw [← List.drop_eq_getElem_cons hlt, List.take_append_drop]
    conv_rhs => rw [hsplit]
    rw [insertSortedU_eq_of_split v d _ _ _ hq (hgt hlt), List.append_assoc, List.singleton_append,
      List.drop_eq_getElem_cons hlt]
  · have hk' : k.val = f.val.length := le_antisymm hk hge
    rw [hk', List.take_length, List.drop_length, List.append_nil,
      insertSortedU_eq_append v d f.val (by rw [hk', List.take_length] at hq; exact hq)]

/-! ## `remove` -/

theorem remove_loop_spec (f : Slice (U32 × U32)) (v : U32) (out : alloc.vec.Vec (U32 × U32))
    (i : Usize) (hi : i.val ≤ f.val.length)
    (hout : out.val = (f.val.take i.val).filter fun p => decide (p.1 ≠ v)) :
    formalism.instances.hcol.remove_loop f v out i ⦃ (res : alloc.vec.Vec (U32 × U32)) =>
      res.val = f.val.filter fun p => decide (p.1 ≠ v) ⦄ := by
  unfold formalism.instances.hcol.remove_loop
  apply loop.spec_decr_nat (measure := fun (st : alloc.vec.Vec (U32 × U32) × Usize) =>
      f.val.length - st.2.val)
    (inv := fun (st : alloc.vec.Vec (U32 × U32) × Usize) => st.2.val ≤ f.val.length ∧
      st.1.val = (f.val.take st.2.val).filter fun p => decide (p.1 ≠ v))
  · rintro ⟨out1, i1⟩ ⟨hi1, hout1⟩
    replace hi1 : i1.val ≤ f.val.length := hi1
    replace hout1 : out1.val = (f.val.take i1.val).filter fun p => decide (p.1 ≠ v) := hout1
    show formalism.instances.hcol.remove_loop.body f v out1 i1 ⦃ _ ⦄
    unfold formalism.instances.hcol.remove_loop.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : i1.val < f.val.length := by scalar_tac
      apply WP.spec_bind (Slice.index_usize_spec f i1 hlt')
      rintro ⟨i2, i3⟩ hp
      have hp' : (i2, i3) = f.val[i1.val] := hp
      have hlen1 : out1.val.length < Usize.max := by
        have h1 := List.length_filter_le (fun p : U32 × U32 => decide (p.1 ≠ v)) (f.val.take i1.val)
        have := f.length_ineq
        rw [← hout1, List.length_take] at h1
        omega
      have hnext : (f.val.take (i1.val + 1)).filter (fun p => decide (p.1 ≠ v)) =
          ((f.val.take i1.val).filter fun p => decide (p.1 ≠ v)) ++
            if i2 ≠ v then [(i2, i3)] else [] := by
        rw [List.take_succ_eq_append_getElem hlt', List.filter_append, ← hp', List.filter_cons,
          List.filter_nil]
        by_cases h : i2 ≠ v
        · rw [if_pos (decide_eq_true h), if_pos h]
        · rw [if_neg (fun h' => h (decide_eq_true_iff.mp h')), if_neg h]
      -- the tail, after the conditional push
      have htail : ∀ (out2 : alloc.vec.Vec (U32 × U32)),
          out2.val = (f.val.take (i1.val + 1)).filter (fun p => decide (p.1 ≠ v)) →
          (do
            let i4 ← i1 + 1#usize
            ok (ControlFlow.cont (out2, i4)) :
            Result (ControlFlow ((alloc.vec.Vec (U32 × U32)) × Usize) (alloc.vec.Vec (U32 × U32))))
          ⦃ (r : ControlFlow ((alloc.vec.Vec (U32 × U32)) × Usize) (alloc.vec.Vec (U32 × U32))) =>
            match r with
            | .cont st => (st.2.val ≤ f.val.length ∧
                st.1.val = (f.val.take st.2.val).filter fun p => decide (p.1 ≠ v)) ∧
                f.val.length - st.2.val < f.val.length - i1.val
            | .done res => res.val = f.val.filter fun p => decide (p.1 ≠ v) ⦄ := by
        intro out2 hout2
        apply WP.spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
        intro i4 hi4
        replace hi4 : i4.val = i1.val + (1#usize).val := hi4
        have hi4' : i4.val = i1.val + 1 := by scalar_tac
        rw [WP.spec_ok]
        show (i4.val ≤ f.val.length ∧ out2.val = _) ∧ f.val.length - i4.val < f.val.length - i1.val
        rw [hi4']
        exact ⟨⟨by omega, hout2⟩, by omega⟩
      apply spec_bind_ite
      · intro hne
        have hne' : i2 ≠ v := bne_iff_ne.mp hne
        apply WP.spec_bind (alloc.vec.Vec.push_spec out1 (i2, i3) hlen1)
        intro out2 hout2
        replace hout2 : out2.val = out1.val ++ [(i2, i3)] := hout2
        apply htail out2
        rw [hnext, if_pos hne', hout2, hout1]
      · intro hne
        have heq : i2 = v := by
          by_contra h
          exact hne (bne_iff_ne.mpr h)
        apply spec_bind_ok
        apply htail out1
        rw [hnext, if_neg (fun h => h heq), List.append_nil, hout1]
    · rename_i hge
      have hin : i1.val = f.val.length := by scalar_tac
      rw [WP.spec_ok, hout1, hin, List.take_length]
  · exact ⟨hi, hout⟩

theorem remove_spec (f : Slice (U32 × U32)) (v : U32) :
    formalism.instances.hcol.remove f v ⦃ (res : alloc.vec.Vec (U32 × U32)) =>
      res.val = f.val.filter fun p => decide (p.1 ≠ v) ⦄ := by
  unfold formalism.instances.hcol.remove
  exact remove_loop_spec f v (alloc.vec.Vec.new _) 0#usize (by simp) (by rw [new_val]; simp)

theorem ofPairs_filter_ne (v : U32) :
    ∀ l : List (U32 × U32),
      ofPairs (l.filter fun p => decide (p.1 ≠ v)) = remove (ofPairs l) v.val
  | [] => rfl
  | p :: rest => by
    rw [remove, ofPairs_cons, List.filter_cons, List.filter_cons]
    by_cases h : p.1 = v
    · rw [if_neg (fun h' => (decide_eq_true_iff.mp h') h),
        if_neg (fun h' => (decide_eq_true_iff.mp h') (by show p.1.val = v.val; rw [h]))]
      exact ofPairs_filter_ne v rest
    · rw [if_pos (decide_eq_true h),
        if_pos (decide_eq_true (show p.1.val ≠ v.val from fun h' => h (UScalar.val_eq_imp _ _ h'))),
        ofPairs_cons, ofPairs_filter_ne v rest, remove]

/-! ## `same`, `PartialEq`, `Clone` -/

theorem same_loop_spec (a b : Slice (U32 × U32)) (e eq0 : Bool) (i : Usize)
    (hi : i.val ≤ a.val.length) (hib : i.val ≤ b.val.length)
    (hinv : eq0 = true ↔ e = true ∧ ∀ j, j < i.val →
      ∀ (ha : j < a.val.length) (hb : j < b.val.length), a.val[j] = b.val[j]) :
    formalism.instances.hcol.same_loop a b eq0 i ⦃ (r : Bool) =>
      r = true ↔ e = true ∧ ∀ j, j < min a.val.length b.val.length →
        ∀ (ha : j < a.val.length) (hb : j < b.val.length), a.val[j] = b.val[j] ⦄ := by
  unfold formalism.instances.hcol.same_loop
  apply loop.spec_decr_nat (measure := fun (st : Bool × Usize) =>
      min a.val.length b.val.length - st.2.val)
    (inv := fun (st : Bool × Usize) => st.2.val ≤ a.val.length ∧ st.2.val ≤ b.val.length ∧
      (st.1 = true ↔ e = true ∧ ∀ j, j < st.2.val →
        ∀ (ha : j < a.val.length) (hb : j < b.val.length), a.val[j] = b.val[j]))
  · rintro ⟨eq1, i1⟩ ⟨hia, hib1, hinv1⟩
    replace hia : i1.val ≤ a.val.length := hia
    replace hib1 : i1.val ≤ b.val.length := hib1
    replace hinv1 : eq1 = true ↔ e = true ∧ ∀ j, j < i1.val →
      ∀ (ha : j < a.val.length) (hb : j < b.val.length), a.val[j] = b.val[j] := hinv1
    show formalism.instances.hcol.same_loop.body a b eq1 i1 ⦃ _ ⦄
    unfold formalism.instances.hcol.same_loop.body
    dsimp only
    split
    · rename_i hlta
      have hlta' : i1.val < a.val.length := by scalar_tac
      split
      · rename_i hltb
        have hltb' : i1.val < b.val.length := by scalar_tac
        apply WP.spec_bind (Slice.index_usize_spec a i1 hlta')
        rintro ⟨i3, i4⟩ hpa
        have hpa' : (i3, i4) = a.val[i1.val] := hpa
        apply WP.spec_bind (Slice.index_usize_spec b i1 hltb')
        rintro ⟨i5, i6⟩ hpb
        have hpb' : (i5, i6) = b.val[i1.val] := hpb
        -- the new flag, then the counter
        have hstep : ∀ (eq2 : Bool), (eq2 = true ↔ eq1 = true ∧ a.val[i1.val] = b.val[i1.val]) →
            (do
              let i7 ← i1 + 1#usize
              ok (ControlFlow.cont (eq2, i7)) : Result (ControlFlow (Bool × Usize) Bool))
            ⦃ (r : ControlFlow (Bool × Usize) Bool) =>
              match r with
              | .cont st => (st.2.val ≤ a.val.length ∧ st.2.val ≤ b.val.length ∧
                  (st.1 = true ↔ e = true ∧ ∀ j, j < st.2.val →
                    ∀ (ha : j < a.val.length) (hb : j < b.val.length), a.val[j] = b.val[j])) ∧
                  min a.val.length b.val.length - st.2.val <
                    min a.val.length b.val.length - i1.val
              | .done r => r = true ↔ e = true ∧ ∀ j, j < min a.val.length b.val.length →
                  ∀ (ha : j < a.val.length) (hb : j < b.val.length), a.val[j] = b.val[j] ⦄ := by
          intro eq2 heq2
          apply WP.spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
          intro i7 hi7
          replace hi7 : i7.val = i1.val + (1#usize).val := hi7
          have hi7' : i7.val = i1.val + 1 := by scalar_tac
          rw [WP.spec_ok]
          show (i7.val ≤ a.val.length ∧ i7.val ≤ b.val.length ∧ (eq2 = true ↔ _)) ∧
            min a.val.length b.val.length - i7.val < min a.val.length b.val.length - i1.val
          refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
          rw [heq2, hinv1, hi7']
          constructor
          · rintro ⟨⟨he, hall⟩, hcur⟩
            refine ⟨he, ?_⟩
            intro j hj ha hb
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
            · exact hall j hj ha hb
            · exact hcur
          · rintro ⟨he, hall⟩
            exact ⟨⟨he, fun j hj ha hb => hall j (Nat.lt_succ_of_lt hj) ha hb⟩,
              hall i1.val (Nat.lt_succ_self _) hlta' hltb'⟩
        have hpair : a.val[i1.val] = b.val[i1.val] ↔ i3 = i5 ∧ i4 = i6 := by
          rw [← hpa', ← hpb', Prod.mk.injEq]
        apply spec_bind_ite
        · intro hne
          have hne' : i3 ≠ i5 := bne_iff_ne.mp hne
          apply spec_bind_ok
          apply hstep
          rw [hpair]
          exact ⟨fun h => nomatch h, fun h => absurd h.2.1 hne'⟩
        · intro hne
          have heq35 : i3 = i5 := by
            by_contra h
            exact hne (bne_iff_ne.mpr h)
          apply spec_bind_ite
          · intro hne2
            have hne2' : i4 ≠ i6 := bne_iff_ne.mp hne2
            apply spec_bind_ok
            apply hstep
            rw [hpair]
            exact ⟨fun h => nomatch h, fun h => absurd h.2.2 hne2'⟩
          · intro hne2
            have heq46 : i4 = i6 := by
              by_contra h
              exact hne2 (bne_iff_ne.mpr h)
            apply spec_bind_ok
            apply hstep
            rw [hpair]
            exact ⟨fun h => ⟨h, heq35, heq46⟩, fun h => h.1⟩
      · rename_i hgeb
        have hin : i1.val = b.val.length := by scalar_tac
        rw [WP.spec_ok]
        have hmin : min a.val.length b.val.length = i1.val := by omega
        rw [hmin]
        exact hinv1
    · rename_i hgea
      have hin : i1.val = a.val.length := by scalar_tac
      rw [WP.spec_ok]
      have hmin : min a.val.length b.val.length = i1.val := by omega
      rw [hmin]
      exact hinv1
  · exact ⟨hi, hib, hinv⟩

theorem same_spec (a b : Slice (U32 × U32)) :
    formalism.instances.hcol.same a b ⦃ (r : Bool) => r = decide (a.val = b.val) ⦄ := by
  unfold formalism.instances.hcol.same
  try dsimp only
  apply WP.spec_mono (same_loop_spec a b (decide (Slice.len a = Slice.len b))
    (decide (Slice.len a = Slice.len b)) 0#usize (by simp) (by simp)
    (by
      constructor
      · intro h
        exact ⟨h, fun j hj => absurd hj (by simp)⟩
      · intro h
        exact h.1))
  intro r hr
  rw [Bool.eq_iff_iff, hr, decide_eq_true_iff, decide_eq_true_iff, UScalar.eq_equiv,
    Slice.len_val, Slice.len_val]
  constructor
  · rintro ⟨hlen, hall⟩
    apply List.ext_getElem hlen
    intro j ha hb
    exact hall j (by omega) ha hb
  · intro h
    refine ⟨by show a.val.length = b.val.length; rw [h], ?_⟩
    intro j _ ha hb
    rw [List.getElem_of_eq h ha]

theorem eq_spec : EqSpec inst.corecmpPartialEqInst := by
  intro a b
  show formalism.instances.hcol.Tau.Insts.CoreCmpPartialEqTau.eq a b ⦃ _ ⦄
  unfold formalism.instances.hcol.Tau.Insts.CoreCmpPartialEqTau.eq
  try dsimp only
  apply WP.spec_mono (same_spec (alloc.vec.Vec.deref a) (alloc.vec.Vec.deref b))
  intro r hr
  rw [hr, deref_val, deref_val, decide_eq_true_iff]
  exact (alloc.vec.Vec.eq_iff a b).symm

theorem clone_loop_spec (self : formalism.instances.hcol.Tau) (out : alloc.vec.Vec (U32 × U32))
    (i : Usize) (hi : i.val ≤ self.val.length) (hout : out.val = self.val.take i.val) :
    formalism.instances.hcol.Tau.Insts.CoreCloneClone.clone_loop self out i
      ⦃ (res : alloc.vec.Vec (U32 × U32)) => res.val = self.val ⦄ := by
  unfold formalism.instances.hcol.Tau.Insts.CoreCloneClone.clone_loop
  apply loop.spec_decr_nat
    (measure := fun (st : formalism.instances.hcol.Tau × alloc.vec.Vec (U32 × U32) × Usize) =>
      self.val.length - st.2.2.val)
    (inv := fun (st : formalism.instances.hcol.Tau × alloc.vec.Vec (U32 × U32) × Usize) =>
      st.1 = self ∧ st.2.2.val ≤ self.val.length ∧ st.2.1.val = self.val.take st.2.2.val)
  · rintro ⟨self1, out1, i1⟩ ⟨hself1, hi1, hout1⟩
    replace hself1 : self1 = self := hself1
    replace hi1 : i1.val ≤ self.val.length := hi1
    replace hout1 : out1.val = self.val.take i1.val := hout1
    subst hself1
    show formalism.instances.hcol.Tau.Insts.CoreCloneClone.clone_loop.body self1 out1 i1 ⦃ _ ⦄
    unfold formalism.instances.hcol.Tau.Insts.CoreCloneClone.clone_loop.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : i1.val < self1.val.length := by scalar_tac
      rw [alloc.vec.Vec.index_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec self1 i1 hlt')
      intro p hp
      replace hp : p = self1.val[i1.val] := hp
      have hlen1 : out1.val.length < Usize.max := by
        have := self1.property
        rw [hout1, List.length_take]
        omega
      apply WP.spec_bind (alloc.vec.Vec.push_spec out1 p hlen1)
      intro out2 hout2
      replace hout2 : out2.val = out1.val ++ [p] := hout2
      apply WP.spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
      intro i2 hi2
      replace hi2 : i2.val = i1.val + (1#usize).val := hi2
      have hi2' : i2.val = i1.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨⟨by first | exact rfl | trivial, by scalar_tac, ?_⟩, by scalar_tac⟩
      rw [hout2, hout1, hp, hi2', List.take_succ_eq_append_getElem hlt']
    · rename_i hge
      have hin : i1.val = self1.val.length := by scalar_tac
      simp only [WP.spec_ok]
      rw [hout1, hin, List.take_length]
  · exact ⟨rfl, hi, hout⟩

theorem clone_spec (a : formalism.instances.hcol.Tau) :
    inst.corecloneCloneInst.clone a ⦃ (r : formalism.instances.hcol.Tau) => r = a ⦄ := by
  show formalism.instances.hcol.Tau.Insts.CoreCloneClone.clone a ⦃ _ ⦄
  unfold formalism.instances.hcol.Tau.Insts.CoreCloneClone.clone
  apply WP.spec_bind (clone_loop_spec a (alloc.vec.Vec.new _) 0#usize (by simp)
    (by rw [new_val]; simp))
  intro out hout
  replace hout : out.val = a.val := hout
  rw [WP.spec_ok]
  exact alloc.vec.Vec.ext _ _ hout

/-! ## `accept` -/

theorem accept_spec (p : formalism.instances.hcol.HColoring) (t : formalism.instances.hcol.Tau) :
    inst.accept p t ⦃ (b : Bool) => b = acceptL (tauOf t) ⦄ := by
  show alloc.vec.Vec.is_empty t ⦃ _ ⦄
  unfold alloc.vec.Vec.is_empty
  rw [WP.spec_ok]
  unfold acceptL tauOf ofPairs
  apply decide_eq_decide.mpr
  rw [List.map_eq_nil_iff]
  exact List.length_eq_zero_iff

/-! ## `consistent` -/

/-- The flag after one pair: it stays unless the pair's `G`-edge to `v` has no `H`-edge. -/
theorem flag_spec (ok1 e h : Bool) :
    (if e then (if (!h) then ok false else ok ok1) else ok ok1 : Result Bool)
      ⦃ (r : Bool) => r = true ↔ ok1 = true ∧ (e = true → h = true) ⦄ := by
  apply spec_ite
  · intro he
    apply spec_ite
    · intro hh
      rw [WP.spec_ok]
      have hh' : h = false := by
        cases h with
        | true => exact absurd hh (by simp)
        | false => rfl
      exact ⟨fun h' => nomatch h', fun h' => absurd (h'.2 he) (by rw [hh']; simp)⟩
    · intro hh
      rw [WP.spec_ok]
      have hh' : h = true := by
        cases h with
        | true => rfl
        | false => exact absurd rfl (by simpa using hh)
      exact ⟨fun h' => ⟨h', fun _ => hh'⟩, fun h' => h'.1⟩
  · intro he
    rw [WP.spec_ok]
    exact ⟨fun h' => ⟨h', fun h'' => absurd h'' he⟩, fun h' => h'.1⟩

theorem consistent_loop_spec (self : formalism.instances.hcol.HColoring) (f : Slice (U32 × U32))
    (v d : U32) (ok0 ok1 : Bool) (i : Usize) (hi : i.val ≤ f.val.length)
    (hinv : ok1 = true ↔ ok0 = true ∧ ∀ p ∈ f.val.take i.val,
      adjOf self.g p.1.val v.val = true → adjOf self.h p.2.val d.val = true) :
    formalism.instances.hcol.HColoring.consistent_loop self f v d ok1 i
      ⦃ (res : formalism.instances.hcol.HColoring × Bool) =>
        res.1 = self ∧ (res.2 = true ↔ ok0 = true ∧ ∀ p ∈ f.val,
          adjOf self.g p.1.val v.val = true → adjOf self.h p.2.val d.val = true) ⦄ := by
  unfold formalism.instances.hcol.HColoring.consistent_loop
  apply loop.spec_decr_nat (measure := fun (st : Bool × Usize) => f.val.length - st.2.val)
    (inv := fun (st : Bool × Usize) => st.2.val ≤ f.val.length ∧
      (st.1 = true ↔ ok0 = true ∧ ∀ p ∈ f.val.take st.2.val,
        adjOf self.g p.1.val v.val = true → adjOf self.h p.2.val d.val = true))
  · rintro ⟨ok2, i1⟩ ⟨hi1, hinv1⟩
    replace hi1 : i1.val ≤ f.val.length := hi1
    replace hinv1 : ok2 = true ↔ ok0 = true ∧ ∀ p ∈ f.val.take i1.val,
      adjOf self.g p.1.val v.val = true → adjOf self.h p.2.val d.val = true := hinv1
    show formalism.instances.hcol.HColoring.consistent_loop.body self f v d ok2 i1 ⦃ _ ⦄
    unfold formalism.instances.hcol.HColoring.consistent_loop.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : i1.val < f.val.length := by scalar_tac
      apply WP.spec_bind (Slice.index_usize_spec f i1 hlt')
      rintro ⟨u, c⟩ hp
      have hp' : (u, c) = f.val[i1.val] := hp
      have hnext : ∀ (ok3 : Bool),
          (ok3 = true ↔ ok2 = true ∧
            (adjOf self.g u.val v.val = true → adjOf self.h c.val d.val = true)) →
          (do
            let i2 ← i1 + 1#usize
            ok (ControlFlow.cont (ok3, i2)) :
            Result (ControlFlow (Bool × Usize) (formalism.instances.hcol.HColoring × Bool)))
          ⦃ (r : ControlFlow (Bool × Usize) (formalism.instances.hcol.HColoring × Bool)) =>
            match r with
            | .cont st => (st.2.val ≤ f.val.length ∧
                (st.1 = true ↔ ok0 = true ∧ ∀ p ∈ f.val.take st.2.val,
                  adjOf self.g p.1.val v.val = true → adjOf self.h p.2.val d.val = true)) ∧
                f.val.length - st.2.val < f.val.length - i1.val
            | .done res => res.1 = self ∧ (res.2 = true ↔ ok0 = true ∧ ∀ p ∈ f.val,
                adjOf self.g p.1.val v.val = true → adjOf self.h p.2.val d.val = true) ⦄ := by
        intro ok3 hok3
        apply WP.spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
        intro i2 hi2
        replace hi2 : i2.val = i1.val + (1#usize).val := hi2
        have hi2' : i2.val = i1.val + 1 := by scalar_tac
        rw [WP.spec_ok]
        show (i2.val ≤ f.val.length ∧ (ok3 = true ↔ _)) ∧
          f.val.length - i2.val < f.val.length - i1.val
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [hok3, hinv1, hi2', List.take_succ_eq_append_getElem hlt', ← hp']
        constructor
        · rintro ⟨⟨h0, hall⟩, hcur⟩
          refine ⟨h0, ?_⟩
          intro p hp
          rw [List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · exact hall p hp
          · exact hcur
        · rintro ⟨h0, hall⟩
          exact ⟨⟨h0, fun p hp => hall p (List.mem_append_left _ hp)⟩,
            hall (u, c) (List.mem_append_right _ (List.mem_singleton_self _))⟩
      apply WP.spec_bind (has_edge_spec self.g u v)
      intro e he
      apply WP.spec_bind (has_edge_spec self.h c d)
      intro h hh
      apply WP.spec_bind (flag_spec ok2 e h)
      intro ok3 hok3
      apply hnext ok3
      rw [hok3, he, hh]
    · rename_i hge
      have hin : i1.val = f.val.length := by scalar_tac
      rw [WP.spec_ok]
      refine ⟨rfl, ?_⟩
      rw [hinv1, hin, List.take_length]
  · exact ⟨hi, hinv⟩

theorem consistent_spec (self : formalism.instances.hcol.HColoring) (f : Slice (U32 × U32))
    (v d : U32) :
    formalism.instances.hcol.HColoring.consistent self f v d ⦃ (b : Bool) =>
      b = consistentL (graphsOf self) (ofPairs f.val) v.val d.val ⦄ := by
  unfold formalism.instances.hcol.HColoring.consistent
  apply WP.spec_bind (consistent_loop_spec self f v d true true 0#usize (by simp)
    (by
      constructor
      · intro _
        exact ⟨rfl, fun p hp => absurd hp (by simp)⟩
      · intro _
        rfl))
  rintro ⟨self1, ok1⟩ hp
  have hp' : self1 = self ∧ (ok1 = true ↔ true = true ∧ ∀ p ∈ f.val,
    adjOf self.g p.1.val v.val = true → adjOf self.h p.2.val d.val = true) := hp
  obtain ⟨rfl, hok1⟩ := hp'
  simp only [eq_self_iff_true, true_and] at hok1
  have hfinal : ∀ (b : Bool), (b = true ↔ (∀ p ∈ f.val,
        adjOf self1.g p.1.val v.val = true → adjOf self1.h p.2.val d.val = true) ∧
        (adjOf self1.g v.val v.val = true → adjOf self1.h d.val d.val = true)) →
      b = consistentL (graphsOf self1) (ofPairs f.val) v.val d.val := by
    intro b hb
    rw [Bool.eq_iff_iff, hb]
    unfold consistentL graphsOf
    rw [decide_eq_true_iff]
    simp only
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact h1 p hp
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      intro p hp
      exact h1 (p.1.val, p.2.val) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  apply WP.spec_bind (has_edge_spec self1.g v v)
  intro e he
  apply WP.spec_bind (has_edge_spec self1.h d d)
  intro h hh
  apply WP.spec_mono (flag_spec ok1 e h)
  intro b hb
  apply hfinal
  rw [hb, hok1, he, hh]

/-! ## `step` -/

/-- What one output reads back as. -/
abbrev outOf (o : formalism.instances.hcol.Tau × alloc.vec.Vec (U32 × U32)) :
    TauL × List (Var × Val) :=
  (tauOf o.1, ofPairs o.2.val)

/-- The model's output for colour `d`, at `Introduce v` over the trace `fL`. -/
def introOut (P : Graphs) (fL : TauL) (v : Var) (o : Bool) (d : Val) :
    Option (TauL × List (Var × Val)) :=
  if consistentL P fL v d = true then some (insertSorted fL v d, if o then [(v, d)] else [])
  else none

theorem emit_spec (out : alloc.vec.Vec (formalism.instances.hcol.Tau × alloc.vec.Vec (U32 × U32)))
    (f : Slice (U32 × U32)) (v d : U32) (owner : Bool) (hf : f.val.length < Usize.max)
    (hout : out.val.length < Usize.max) :
    formalism.instances.hcol.HColoring.emit out f v d owner
      ⦃ (res : alloc.vec.Vec (formalism.instances.hcol.Tau × alloc.vec.Vec (U32 × U32))) =>
        res.val.map outOf = out.val.map outOf ++
          [(insertSorted (ofPairs f.val) v.val d.val, if owner then [(v.val, d.val)] else [])] ⦄ := by
  unfold formalism.instances.hcol.HColoring.emit
  have hleaves : ∀ (leaves : alloc.vec.Vec (U32 × U32)),
      ofPairs leaves.val = (if owner then [(v.val, d.val)] else []) →
      (do
        let v1 ← formalism.instances.hcol.insert_sorted f v d
        alloc.vec.Vec.push out (v1, leaves) :
        Result (alloc.vec.Vec (formalism.instances.hcol.Tau × alloc.vec.Vec (U32 × U32))))
      ⦃ (res : alloc.vec.Vec (formalism.instances.hcol.Tau × alloc.vec.Vec (U32 × U32))) =>
        res.val.map outOf = out.val.map outOf ++
          [(insertSorted (ofPairs f.val) v.val d.val, if owner then [(v.val, d.val)] else [])] ⦄ := by
    intro leaves hl
    apply WP.spec_bind (insert_sorted_spec f v d hf)
    intro v1 hv1
    replace hv1 : v1.val = insertSortedU f.val v d := hv1
    apply WP.spec_mono (alloc.vec.Vec.push_spec out (v1, leaves) hout)
    intro res hres
    rw [hres, List.map_append, List.map_singleton]
    show _ = _ ++ [(ofPairs v1.val, ofPairs leaves.val)]
    rw [hv1, ofPairs_insertSortedU, hl]
  apply spec_bind_ite
  · intro ho
    apply WP.spec_bind (alloc.vec.Vec.push_spec (alloc.vec.Vec.new _) (v, d) new_len)
    intro leaves hl
    replace hl : leaves.val = (alloc.vec.Vec.new (U32 × U32)).val ++ [(v, d)] := hl
    rw [new_val, List.nil_append] at hl
    apply hleaves leaves
    rw [hl, if_pos ho]
    rfl
  · intro ho
    apply spec_bind_ok
    apply hleaves (alloc.vec.Vec.new _)
    rw [new_val, if_neg ho]
    rfl

theorem step_loop_spec (self : formalism.instances.hcol.HColoring) (v : U32) (owner : Bool)
    (f : alloc.vec.Vec (U32 × U32)) (hf : f.val.length < Usize.max)
    (out : alloc.vec.Vec (formalism.instances.hcol.Tau × alloc.vec.Vec (U32 × U32))) (d : U32)
    (hd : d.val ≤ (graphsOf self).nH) (hlen : out.val.length ≤ d.val)
    (hout : out.val.map outOf =
      (List.range d.val).filterMap (introOut (graphsOf self) (ofPairs f.val) v.val owner)) :
    formalism.instances.hcol.HColoring.Insts.FormalismSchemeTracedOpTau.step_loop self v owner out
        f d
      ⦃ (res : alloc.vec.Vec (formalism.instances.hcol.Tau × alloc.vec.Vec (U32 × U32))) =>
        res.val.map outOf = (List.range (graphsOf self).nH).filterMap
          (introOut (graphsOf self) (ofPairs f.val) v.val owner) ⦄ := by
  unfold formalism.instances.hcol.HColoring.Insts.FormalismSchemeTracedOpTau.step_loop
  apply loop.spec_decr_nat
    (measure := fun (st : alloc.vec.Vec (formalism.instances.hcol.Tau ×
      alloc.vec.Vec (U32 × U32)) × U32) => (graphsOf self).nH - st.2.val)
    (inv := fun (st : alloc.vec.Vec (formalism.instances.hcol.Tau ×
      alloc.vec.Vec (U32 × U32)) × U32) => st.2.val ≤ (graphsOf self).nH ∧
      st.1.val.length ≤ st.2.val ∧
      st.1.val.map outOf =
        (List.range st.2.val).filterMap (introOut (graphsOf self) (ofPairs f.val) v.val owner))
  · rintro ⟨out1, d1⟩ ⟨hd1, hlen1, hout1⟩
    replace hd1 : d1.val ≤ (graphsOf self).nH := hd1
    replace hlen1 : out1.val.length ≤ d1.val := hlen1
    replace hout1 : out1.val.map outOf =
      (List.range d1.val).filterMap (introOut (graphsOf self) (ofPairs f.val) v.val owner) := hout1
    show formalism.instances.hcol.HColoring.Insts.FormalismSchemeTracedOpTau.step_loop.body self v
      owner f out1 d1 ⦃ _ ⦄
    unfold formalism.instances.hcol.HColoring.Insts.FormalismSchemeTracedOpTau.step_loop.body
    apply spec_bind_ok
    apply spec_bind_ok
    have hnH : (UScalar.cast .U32 (alloc.vec.Vec.len self.h.adj)).val = (graphsOf self).nH := by
      rw [UScalar.cast_val_eq, alloc.vec.Vec.len_val, UScalarTy.U32_numBits_eq, graphsOf_nH]
      rfl
    try dsimp only
    apply spec_ite
    · intro hlt
      have hlt' : d1.val < (graphsOf self).nH := by
        rw [UScalar.lt_equiv, hnH] at hlt
        exact hlt
      have hnHle : (graphsOf self).nH ≤ Usize.max := by
        rw [graphsOf_nH]
        exact (Nat.mod_le _ _).trans self.h.adj.property
      have hd1max : d1.val + 1 ≤ U32.max := by
        have := UScalar.hBounds (UScalar.cast .U32 (alloc.vec.Vec.len self.h.adj))
        rw [hnH, UScalarTy.U32_numBits_eq] at this
        rw [U32.max_eq]
        omega
      apply WP.spec_bind (consistent_spec self (alloc.vec.Vec.deref f) v d1)
      intro c hc
      rw [deref_val] at hc
      -- the counter, from any state the conditional emit can leave
      have htail : ∀ (out2 : alloc.vec.Vec (formalism.instances.hcol.Tau ×
            alloc.vec.Vec (U32 × U32))),
          out2.val.length ≤ d1.val + 1 →
          out2.val.map outOf = (List.range (d1.val + 1)).filterMap
            (introOut (graphsOf self) (ofPairs f.val) v.val owner) →
          (do
            let d2 ← d1 + 1#u32
            ok (ControlFlow.cont (out2, d2)) :
            Result (ControlFlow ((alloc.vec.Vec (formalism.instances.hcol.Tau ×
              alloc.vec.Vec (U32 × U32))) × U32)
              (alloc.vec.Vec (formalism.instances.hcol.Tau × alloc.vec.Vec (U32 × U32)))))
          ⦃ (r : ControlFlow ((alloc.vec.Vec (formalism.instances.hcol.Tau ×
              alloc.vec.Vec (U32 × U32))) × U32)
              (alloc.vec.Vec (formalism.instances.hcol.Tau × alloc.vec.Vec (U32 × U32)))) =>
            match r with
            | .cont st => (st.2.val ≤ (graphsOf self).nH ∧ st.1.val.length ≤ st.2.val ∧
                st.1.val.map outOf = (List.range st.2.val).filterMap
                  (introOut (graphsOf self) (ofPairs f.val) v.val owner)) ∧
                (graphsOf self).nH - st.2.val < (graphsOf self).nH - d1.val
            | .done res => res.val.map outOf = (List.range (graphsOf self).nH).filterMap
                (introOut (graphsOf self) (ofPairs f.val) v.val owner) ⦄ := by
        intro out2 hlen2 hout2
        apply WP.spec_bind (U32.add_spec (x := d1) (y := 1#u32) (by scalar_tac))
        intro d2 hd2
        replace hd2 : d2.val = d1.val + (1#u32).val := hd2
        have hd2' : d2.val = d1.val + 1 := by scalar_tac
        rw [WP.spec_ok]
        show (d2.val ≤ (graphsOf self).nH ∧ out2.val.length ≤ d2.val ∧ out2.val.map outOf = _) ∧
          (graphsOf self).nH - d2.val < (graphsOf self).nH - d1.val
        rw [hd2']
        exact ⟨⟨hlt', hlen2, hout2⟩, by omega⟩
      apply spec_bind_ite
      · intro hcons
        have hcons' : consistentL (graphsOf self) (ofPairs f.val) v.val d1.val = true := by
          rw [← hc]; exact hcons
        apply WP.spec_bind (emit_spec out1 (alloc.vec.Vec.deref f) v d1 owner
          (by rw [deref_val]; exact hf) (by omega))
        intro out2 hout2
        rw [deref_val] at hout2
        apply htail out2
        · have := congrArg List.length hout2
          rw [List.length_map, List.length_append, List.length_map, List.length_singleton] at this
          omega
        · rw [hout2, hout1]
          simp only [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
            introOut, hcons', if_true]
      · intro hcons
        have hcons' : consistentL (graphsOf self) (ofPairs f.val) v.val d1.val ≠ true := by
          rw [← hc]; exact hcons
        apply spec_bind_ok
        apply htail out1 (by omega)
        rw [hout1]
        simp only [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
          introOut, if_neg hcons', List.append_nil]
    · intro hge
      have hge' : (graphsOf self).nH ≤ d1.val := by
        rw [UScalar.lt_equiv, hnH] at hge
        omega
      have hd : d1.val = (graphsOf self).nH := le_antisymm hd1 hge'
      rw [WP.spec_ok, hout1, hd]
  · exact ⟨hd, hlen, hout⟩

theorem step_spec (p : formalism.instances.hcol.HColoring) (op : formalism.instances.hcol.Op)
    (s : Slice formalism.instances.hcol.Tau) (hok : hcolOk (R.opOf op) (s.val.map R.tauOf)) :
    inst.step p op s ⦃ (outs : alloc.vec.Vec (formalism.instances.hcol.Tau ×
        alloc.vec.Vec (U32 × U32))) =>
      outs.val.map (fun o => (R.tauOf o.1, ofPairs o.2.val)) =
        (instL (graphsOf p)).step (R.opOf op) (s.val.map R.tauOf) ⦄ := by
  show formalism.instances.hcol.HColoring.Insts.FormalismSchemeTracedOpTau.step p op s ⦃ _ ⦄
  unfold formalism.instances.hcol.HColoring.Insts.FormalismSchemeTracedOpTau.step
  obtain ⟨hfit, harity⟩ := hok
  rw [instL_step]
  cases op with
  | Leaf =>
    apply WP.spec_mono (alloc.vec.Vec.push_spec (alloc.vec.Vec.new _) _ new_len)
    intro outs houts
    rw [houts, new_val, List.nil_append]
    rfl
  | Introduce v owner =>
    have hne : s.val ≠ [] := by
      intro h
      apply harity
      show (s.val.map R.tauOf) = []
      rw [h, List.map_nil]
    obtain ⟨t, rest, hs⟩ := List.exists_cons_of_ne_nil hne
    have h0 : (0#usize).val < s.val.length := by rw [hs]; simp
    apply WP.spec_bind (Slice.index_usize_spec s 0#usize h0)
    intro t' ht'
    replace ht' : t' = s.val[(0#usize).val] := ht'
    have ht : t' = t := by rw [ht', hs]; rfl
    subst ht
    have hflen : t'.val.length < Usize.max := by
      have := hfit (R.tauOf t') (by rw [hs, List.map_cons]; exact List.mem_cons_self ..)
      show (ofPairs t'.val).length < Usize.max at this
      rw [ofPairs_length] at this
      exact this
    apply WP.spec_mono (step_loop_spec p v owner t' hflen (alloc.vec.Vec.new _) 0#u32 (by simp)
      (by rw [new_val]; simp) (by rw [new_val]; rfl))
    intro res hres
    rw [hs, List.map_cons]
    show res.val.map outOf = stepL (graphsOf p) (.intro v.val owner) (tauOf t' :: rest.map R.tauOf)
    rw [hres]
    rfl
  | Forget v =>
    have hne : s.val ≠ [] := by
      intro h
      apply harity
      show (s.val.map R.tauOf) = []
      rw [h, List.map_nil]
    obtain ⟨t, rest, hs⟩ := List.exists_cons_of_ne_nil hne
    have h0 : (0#usize).val < s.val.length := by rw [hs]; simp
    apply WP.spec_bind (Slice.index_usize_spec s 0#usize h0)
    intro t' ht'
    replace ht' : t' = s.val[(0#usize).val] := ht'
    have ht : t' = t := by rw [ht', hs]; rfl
    subst ht
    try dsimp only
    apply WP.spec_bind (remove_spec (alloc.vec.Vec.deref t') v)
    intro v1 hv1
    replace hv1 : v1.val = (alloc.vec.Vec.deref t').val.filter fun q => decide (q.1 ≠ v) := hv1
    rw [deref_val] at hv1
    apply WP.spec_mono (alloc.vec.Vec.push_spec (alloc.vec.Vec.new _) _ new_len)
    intro outs houts
    rw [houts, new_val, List.nil_append, hs, List.map_cons]
    show [(tauOf v1, ofPairs (alloc.vec.Vec.new (U32 × U32)).val)] =
      stepL (graphsOf p) (.forget v.val) (tauOf t' :: rest.map R.tauOf)
    rw [new_val]
    show [(ofPairs v1.val, [])] = [(remove (ofPairs t'.val) v.val, [])]
    rw [hv1, ofPairs_filter_ne]
  | Join =>
    have h2 : 2 ≤ s.val.length := by
      have := harity
      show 2 ≤ (s.val.map R.tauOf).length at this
      rw [List.length_map] at this
      exact this
    obtain ⟨t, rest, hs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega))
    have hrest : rest ≠ [] := by
      intro h
      rw [hs, h] at h2
      simp at h2
    obtain ⟨t1, rest', hs'⟩ := List.exists_cons_of_ne_nil hrest
    rw [hs'] at hs
    have h0 : (0#usize).val < s.val.length := by rw [hs]; simp
    have h1 : (1#usize).val < s.val.length := by rw [hs]; simp
    apply WP.spec_bind (Slice.index_usize_spec s 0#usize h0)
    intro ta hta
    replace hta : ta = s.val[(0#usize).val] := hta
    have hta' : ta = t := by rw [hta, hs]; rfl
    subst hta'
    try dsimp only
    apply WP.spec_bind (Slice.index_usize_spec s 1#usize h1)
    intro tb htb
    replace htb : tb = s.val[(1#usize).val] := htb
    have htb' : tb = t1 := by rw [htb, hs]; rfl
    subst htb'
    try dsimp only
    apply WP.spec_bind (same_spec (alloc.vec.Vec.deref ta) (alloc.vec.Vec.deref tb))
    intro b hb
    rw [deref_val, deref_val] at hb
    rw [hs, List.map_cons, List.map_cons]
    subst hb
    apply spec_ite
    · intro heq
      have heq' : ta.val = tb.val := decide_eq_true_iff.mp heq
      have heq'' : ta = tb := alloc.vec.Vec.ext _ _ heq'
      apply WP.spec_bind (clone_spec ta)
      intro t2 ht2
      replace ht2 : t2 = ta := ht2
      subst ht2
      apply WP.spec_mono (alloc.vec.Vec.push_spec (alloc.vec.Vec.new _) _ new_len)
      intro outs houts
      rw [houts, new_val, List.nil_append]
      show [(tauOf t2, ofPairs (alloc.vec.Vec.new (U32 × U32)).val)] =
        (if tauOf t2 = tauOf tb then [(tauOf t2, [])] else [])
      rw [new_val, if_pos (by rw [heq''])]
      rfl
    · intro hne
      have hne' : ta ≠ tb := fun h => hne (decide_eq_true (by rw [h]))
      rw [WP.spec_ok, new_val, List.map_nil]
      show [] = (if tauOf ta = tauOf tb then [(tauOf ta, [])] else [])
      rw [if_neg (fun h => hne' (tauOf_injective h))]

/-- The Rust `HColoring` computes the list model. -/
theorem tracedSpec (p : formalism.instances.hcol.HColoring) :
    TracedSpec R inst p (instL (graphsOf p)).toTraced hcolOk :=
  ⟨eq_spec, clone_spec, step_spec p, fun t => by
    apply WP.spec_mono (accept_spec p t)
    intro b hb
    exact hb⟩

/-- Claim 1 for the extracted `hylo::dp::solve_hcol`: on a well-formed nice tree decomposition
    with an empty root bag that checks every edge of `G` (what `NiceTd::new` validates), whose
    tables fit and whose steps are run where defined, the expression denotes exactly the
    `H`-colourings of `G`. -/
theorem solve_hcol_sound (p : formalism.instances.hcol.HColoring) (m : Node HOp)
    (root : formalism.scheme.Node formalism.instances.hcol.Op) (hrel : NodeRel R root m)
    (hfit : Fits (instL (graphsOf p)).toTraced m)
    (hok : StepsOk (instL (graphsOf p)).toTraced hcolOk m) (hwf : WF m) (hroot : bag m = ∅)
    (hcov : ∀ u ∈ desc m, ∀ w ∈ desc m, (graphsOf p).adjG u w = true →
      (u, w) ∈ covered (graphsOf p) m ∨ (w, u) ∈ covered (graphsOf p) m)
    (hsymm : ∀ c d, (graphsOf p).adjH c d = (graphsOf p).adjH d c) :
    hylo.dp.solve_hcol p root ⦃ (e : formalism.expr.Expr) =>
      Sem (ofExt e) (Hom (graphsOf p) (desc m)) ⦄ := by
  unfold hylo.dp.solve_hcol
  apply WP.spec_mono (solve_spec R inst p (instL (graphsOf p)).toTraced (tracedSpec p) m root hrel
    hfit hok)
  intro e he
  rw [he]
  exact hcol_sound_L (graphsOf p) hwf hroot hcov hsymm

end Formalism.HColRust
