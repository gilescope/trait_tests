import Mathlib
import FormalismVerify.Spec
/-!
# A concrete instance of the trace DP: bit assignments with `k` ones

The smallest instance that exercises every obligation of `Instance`. A construction is a tree
whose leaves each assign one variable a bit and whose inner nodes combine their children; a
construction is well formed when every variable has exactly one leaf. The trace of a partial
candidate is its number of ones, and a solution is a candidate with exactly `k` ones.

`solve_sound` then says, with no further hypothesis, that the DP's expression denotes exactly
the assignments of the tree's variables with `k` ones.
-/

namespace Formalism.Bits
open Formalism Traced

/-- A leaf assigns one variable; an inner node only combines. -/
inductive Op where
  | leaf (v : Var)
  | node

/-- Trace: the number of ones so far. -/
abbrev Tau := ℕ

/-- Mirrors `Traced::step`: a leaf tries both bits, a node sums its children's counts. -/
def step : Op → List Tau → List (Tau × List (Var × Val))
  | .leaf v, taus => [(taus.sum, [(v, 0)]), (taus.sum + 1, [(v, 1)])]
  | .node, taus => [(taus.sum, [])]

/-- The number of variables assigned `1`. -/
def ones (f : Assign) : ℕ := (f.1.filter fun p => p.2 = 1).card

mutual
/-- The variables a construction assigns, in tree order. -/
def leaves : Node Op → List Var
  | .mk (.leaf v) cs => v :: leavesList cs
  | .mk .node cs => leavesList cs
def leavesList : List (Node Op) → List Var
  | [] => []
  | c :: cs => leaves c ++ leavesList cs
end

mutual
/-- All assignments of a construction's variables: one bit per leaf. -/
def cands : Node Op → Finset Assign
  | .mk (.leaf v) cs =>
    (joinedSet (candsList cs) ×ˢ ({Assign.single v 0, Assign.single v 1} : Finset Assign)).image
      fun p => p.1.join p.2
  | .mk .node cs => joinedSet (candsList cs)
def candsList : List (Node Op) → List (Finset Assign)
  | [] => []
  | c :: cs => cands c :: candsList cs
end

theorem candsList_eq : ∀ cs : List (Node Op), candsList cs = cs.map cands
  | [] => rfl
  | c :: cs => by rw [candsList, List.map_cons, candsList_eq cs]

theorem leavesList_eq : ∀ cs : List (Node Op), leavesList cs = cs.flatMap leaves
  | [] => rfl
  | c :: cs => by rw [leavesList, List.flatMap_cons, leavesList_eq cs]

/-- Well formed: every variable at exactly one leaf. -/
def WF (n : Node Op) : Prop := (leaves n).Nodup

theorem wf_leaves_list {op : Op} {cs : List (Node Op)} (h : WF (.mk op cs)) :
    (cs.flatMap leaves).Nodup := by
  rw [← leavesList_eq]
  cases op with
  | leaf v => exact (List.nodup_cons.mp h).2
  | node => exact h

/-! ### Counting ones -/

theorem ones_join {f g : Assign} (h : Disjoint f.dom g.dom) : ones (f.join g) = ones f + ones g := by
  unfold ones
  rw [Assign.join_val h, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Assign.disjoint_val h)

theorem ones_empty : ones Assign.empty = 0 := by simp [ones, Assign.empty]

theorem ones_single_zero (v : Var) : ones (Assign.single v 0) = 0 := by simp [ones, Assign.single]

theorem ones_single_one (v : Var) : ones (Assign.single v 1) = 1 := by simp [ones, Assign.single]

/-! ### Domains -/

/-- Variables of a left fold of joins, when the pieces are pairwise disjoint and disjoint from
    the start. -/
theorem dom_foldl_join :
    ∀ (fs : List Assign) (e : Assign), (fs.map Assign.dom).Pairwise Disjoint →
      (∀ g ∈ fs, Disjoint e.dom g.dom) →
      (fs.foldl Assign.join e).dom = e.dom ∪ (fs.map Assign.dom).foldr (· ∪ ·) ∅
  | [], e, _, _ => by simp
  | g :: fs, e, hpair, he => by
    rw [List.map_cons, List.pairwise_cons] at hpair
    have hd : Disjoint e.dom g.dom := he g (List.mem_cons_self ..)
    have ih := dom_foldl_join fs (e.join g) hpair.2 (fun g' hg' => by
      rw [Assign.join_dom hd, Finset.disjoint_union_left]
      exact ⟨he g' (List.mem_cons_of_mem _ hg'), hpair.1 _ (List.mem_map.mpr ⟨g', hg', rfl⟩)⟩)
    rw [List.foldl_cons, ih, Assign.join_dom hd, List.map_cons, List.foldr_cons,
      Finset.union_assoc]

theorem map_eq_of_forall₂ {α β γ : Type*} {g : α → γ} {h : β → γ} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ (fun a b => g a = h b) as bs → as.map g = bs.map h
  | [], [], _ => rfl
  | [], _ :: _, hF => nomatch hF
  | _ :: _, [], hF => nomatch hF
  | a :: as, b :: bs, hF => by
    rw [List.forall₂_cons] at hF
    rw [List.map_cons, List.map_cons, hF.1, map_eq_of_forall₂ hF.2]

theorem foldr_union_toFinset :
    ∀ cs : List (Node Op),
      (cs.map fun c => (leaves c).toFinset).foldr (· ∪ ·) ∅ = (cs.flatMap leaves).toFinset
  | [] => by simp
  | c :: cs => by
    rw [List.map_cons, List.foldr_cons, List.flatMap_cons, List.toFinset_append,
      foldr_union_toFinset cs]

theorem pairwise_dom_of_wf {op : Op} {cs : List (Node Op)} (h : WF (.mk op cs)) :
    (cs.map fun c => (leaves c).toFinset).Pairwise Disjoint := by
  rw [List.pairwise_map]
  have hnd := wf_leaves_list h
  rw [List.nodup_flatMap] at hnd
  exact hnd.2.imp fun hdisj => List.disjoint_toFinset_iff_disjoint.mpr hdisj

theorem wf_children {op : Op} {cs : List (Node Op)} (h : WF (.mk op cs)) : ∀ c ∈ cs, WF c := by
  have hnd := wf_leaves_list h
  rw [List.nodup_flatMap] at hnd
  exact hnd.1

/-- The domain of a join of one candidate per child, when each child's candidates have that
    child's variables. -/
theorem dom_joinAll_of_forall₂ {cs : List (Node Op)} {fs : List Assign} {op : Op}
    (h : WF (.mk op cs)) (hF : List.Forall₂ (fun f c => f.dom = (leaves c).toFinset) fs cs) :
    (Assign.joinAll fs).dom = (cs.flatMap leaves).toFinset := by
  have hmap : fs.map Assign.dom = cs.map fun c => (leaves c).toFinset := map_eq_of_forall₂ hF
  unfold Assign.joinAll
  rw [dom_foldl_join fs Assign.empty (hmap ▸ pairwise_dom_of_wf h)
    (fun _ _ => by rw [Assign.empty_dom]; exact Finset.disjoint_empty_left _),
    Assign.empty_dom, Finset.empty_union, hmap, foldr_union_toFinset]

theorem leaf_not_mem {v : Var} {cs : List (Node Op)} (h : WF (.mk (.leaf v) cs)) :
    v ∉ cs.flatMap leaves := by
  rw [← leavesList_eq]
  exact (List.nodup_cons.mp h).1

mutual
theorem dom_eq : ∀ n : Node Op, WF n → ∀ f ∈ cands n, f.dom = (leaves n).toFinset
  | .mk (.leaf v) cs, h, f, hf => by
    rw [cands, Finset.mem_image] at hf
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hf
    rw [Finset.mem_product] at hab
    obtain ⟨ha, hb⟩ := hab
    rw [mem_joinedSet, candsList_eq] at ha
    obtain ⟨fs, hfs, rfl⟩ := ha
    have hda := dom_joinAll_of_forall₂ h (dom_eq_list cs (wf_children h) fs
      ((List.forall₂_map_right_iff).mp hfs))
    have hbd : b.dom = {v} := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl <;> exact Assign.single_dom _ _
    have hd : Disjoint (Assign.joinAll fs).dom b.dom := by
      rw [hda, hbd, Finset.disjoint_singleton_right, List.mem_toFinset]
      exact leaf_not_mem h
    rw [Assign.join_dom hd, hda, hbd, leaves, leavesList_eq, List.toFinset_cons, Finset.insert_eq,
      Finset.union_comm]
  | .mk .node cs, h, f, hf => by
    rw [cands, mem_joinedSet, candsList_eq] at hf
    obtain ⟨fs, hfs, rfl⟩ := hf
    rw [leaves, leavesList_eq]
    exact dom_joinAll_of_forall₂ h (dom_eq_list cs (wf_children h) fs
      ((List.forall₂_map_right_iff).mp hfs))
theorem dom_eq_list :
    ∀ cs : List (Node Op), (∀ c ∈ cs, WF c) → ∀ fs : List Assign,
      List.Forall₂ (fun f c => f ∈ cands c) fs cs →
      List.Forall₂ (fun f c => f.dom = (leaves c).toFinset) fs cs
  | [], _, [], _ => List.Forall₂.nil
  | [], _, _ :: _, hF => nomatch hF
  | _ :: _, _, [], hF => nomatch hF
  | c :: cs, hcs, f :: fs, hF => by
    rw [List.forall₂_cons] at hF
    exact List.Forall₂.cons (dom_eq c (hcs c (List.mem_cons_self ..)) f hF.1)
      (dom_eq_list cs (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) fs hF.2)
end

/-! ### Traces -/

/-- The ones of a left fold of joins add up, when the pieces are pairwise disjoint and disjoint
    from the start. -/
theorem ones_foldl_join :
    ∀ (fs : List Assign) (e : Assign), (fs.map Assign.dom).Pairwise Disjoint →
      (∀ g ∈ fs, Disjoint e.dom g.dom) →
      ones (fs.foldl Assign.join e) = ones e + (fs.map ones).sum
  | [], e, _, _ => by simp
  | g :: fs, e, hpair, he => by
    rw [List.map_cons, List.pairwise_cons] at hpair
    have hd : Disjoint e.dom g.dom := he g (List.mem_cons_self ..)
    have ih := ones_foldl_join fs (e.join g) hpair.2 (fun g' hg' => by
      rw [Assign.join_dom hd, Finset.disjoint_union_left]
      exact ⟨he g' (List.mem_cons_of_mem _ hg'), hpair.1 _ (List.mem_map.mpr ⟨g', hg', rfl⟩)⟩)
    rw [List.foldl_cons, ih, ones_join hd, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem zipWith_const_right {α β γ : Type*} (g : β → γ) :
    ∀ (as : List α) (bs : List β), as.length = bs.length →
      List.zipWith (fun _ b => g b) as bs = bs.map g
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zipWith_cons_cons, List.map_cons, zipWith_const_right g as bs h]

/-- The ones of a join of one candidate per child: the children's counts added. -/
theorem ones_joinAll {op : Op} {cs : List (Node Op)} (h : WF (.mk op cs)) {fs : List Assign}
    (hF : List.Forall₂ (fun f c => f ∈ cands c) fs cs) :
    ones (Assign.joinAll fs) = (fs.map ones).sum := by
  have hmap : fs.map Assign.dom = cs.map fun c => (leaves c).toFinset :=
    map_eq_of_forall₂ (dom_eq_list cs (wf_children h) fs hF)
  unfold Assign.joinAll
  rw [ones_foldl_join fs Assign.empty (hmap ▸ pairwise_dom_of_wf h)
    (fun _ _ => by rw [Assign.empty_dom]; exact Finset.disjoint_empty_left _), ones_empty,
    Nat.zero_add]

theorem ofList_leaf (v : Var) (b : Val) : Assign.ofList [(v, b)] = Assign.single v b := by
  rw [Assign.ofList, Assign.ofList, Assign.join_empty]

/-! ### The instance -/

/-- Bit assignments with exactly `k` ones. -/
def inst (k : ℕ) : Instance Op Tau where
  step := step
  accept := fun t => decide (t = k)
  candidates := cands
  trace := fun _ f => ones f
  WF := WF
  wf_children := fun _ _ h => wf_children h
  nodeDom := fun n => (leaves n).toFinset
  dom_eq := dom_eq
  owned := fun op => match op with
    | .leaf v => {v}
    | .node => ∅
  owned_disjoint := by
    intro op cs h c hc
    cases op with
    | node => exact Finset.disjoint_empty_left _
    | leaf v =>
      show Disjoint {v} (leaves c).toFinset
      rw [Finset.disjoint_singleton_left, List.mem_toFinset]
      intro hv
      exact leaf_not_mem h (List.mem_flatMap.mpr ⟨c, hc, hv⟩)
  children_disjoint := fun _ _ h => pairwise_dom_of_wf h
  step_leaves := by
    intro op taus out hout
    cases op with
    | leaf v =>
      simp only [step, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hout
      rcases hout with rfl | rfl <;> simp
    | node =>
      simp only [step, List.mem_singleton] at hout
      subst hout
      simp
  step_nodup := by
    intro op taus
    cases op with
    | leaf v => simp [step, ofList_leaf, Assign.single]
    | node => simp [step]
  cand_iff := by
    intro op cs h f
    cases op with
    | node =>
      rw [cands, mem_joinedSet, candsList_eq]
      constructor
      · rintro ⟨fs, hfs, rfl⟩
        refine ⟨fs, List.forall₂_map_right_iff.mp hfs, _, List.mem_singleton_self _, ?_⟩
        rw [Assign.ofList, Assign.join_empty]
      · rintro ⟨fs, hfs, out, hout, rfl⟩
        simp only [step, List.mem_singleton] at hout
        subst hout
        rw [Assign.ofList, Assign.join_empty]
        exact ⟨fs, List.forall₂_map_right_iff.mpr hfs, rfl⟩
    | leaf v =>
      rw [cands, Finset.mem_image]
      constructor
      · rintro ⟨⟨a, b⟩, hab, rfl⟩
        rw [Finset.mem_product] at hab
        obtain ⟨ha, hb⟩ := hab
        rw [mem_joinedSet, candsList_eq] at ha
        obtain ⟨fs, hfs, rfl⟩ := ha
        refine ⟨fs, List.forall₂_map_right_iff.mp hfs, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., by rw [ofList_leaf]⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by rw [ofList_leaf]⟩
      · rintro ⟨fs, hfs, out, hout, rfl⟩
        simp only [step, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hout
        have ha : Assign.joinAll fs ∈ joinedSet (candsList cs) := by
          rw [mem_joinedSet, candsList_eq]
          exact ⟨fs, List.forall₂_map_right_iff.mpr hfs, rfl⟩
        rcases hout with rfl | rfl
        · exact ⟨(Assign.joinAll fs, Assign.single v 0),
            Finset.mem_product.mpr ⟨ha, by simp⟩, by rw [ofList_leaf]⟩
        · exact ⟨(Assign.joinAll fs, Assign.single v 1),
            Finset.mem_product.mpr ⟨ha, by simp⟩, by rw [ofList_leaf]⟩
  trace_mk := by
    intro op cs fs out h hF hout
    have hlen : cs.length = fs.length := (List.Forall₂.length_eq hF).symm
    rw [zipWith_const_right ones cs fs hlen] at hout
    have hsum := ones_joinAll h hF
    have hdom := dom_joinAll_of_forall₂ h (dom_eq_list cs (wf_children h) fs hF)
    cases op with
    | node =>
      simp only [step, List.mem_singleton] at hout
      subst hout
      show ones ((Assign.joinAll fs).join (Assign.ofList [])) = (fs.map ones).sum
      rw [Assign.ofList, Assign.join_empty, hsum]
    | leaf v =>
      have hd : ∀ b, Disjoint (Assign.joinAll fs).dom (Assign.single v b).dom := by
        intro b
        rw [hdom, Assign.single_dom, Finset.disjoint_singleton_right, List.mem_toFinset]
        exact leaf_not_mem h
      simp only [step, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hout
      rcases hout with rfl | rfl
      · show ones ((Assign.joinAll fs).join (Assign.ofList [(v, 0)])) = (fs.map ones).sum
        rw [ofList_leaf, ones_join (hd 0), hsum, ones_single_zero]
      · show ones ((Assign.joinAll fs).join (Assign.ofList [(v, 1)])) = (fs.map ones).sum + 1
        rw [ofList_leaf, ones_join (hd 1), hsum, ones_single_one]
  solution := fun _ f => ones f = k
  accept_iff := fun _ f _ => by simp

/-- Claim 1 for this instance: on a well-formed construction, the DP's expression denotes exactly
    the assignments of its variables with `k` ones. -/
theorem solve_sound (k : ℕ) {n : Node Op} (h : WF n) :
    Sem ((inst k).toTraced.solve n) ((cands n).filter fun f => ones f = k) := by
  have hs := Formalism.solve_sound (inst k) (n := n) h
  have heq : ((inst k).candidates n).filter
      (fun f => (inst k).accept ((inst k).trace n f) = true) =
      (cands n).filter fun f => ones f = k := by
    apply Finset.filter_congr
    intro f _
    simp [inst]
  rw [heq] at hs
  exact hs

end Formalism.Bits
