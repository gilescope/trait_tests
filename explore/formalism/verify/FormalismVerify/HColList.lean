import FormalismVerify.HCol

/-!
# H-colouring with traces as sorted lists

`instances/hcol.rs` keeps a trace as a `Vec<(Var, Val)>` sorted by variable, and its `step`
works on that list (`insert_sorted`, `remove`, element-wise equality). `HCol.lean` proves the
instance with traces as assignments; here the traces are read through `toSorted`, the sorted
list of an assignment's pairs, and `stepL` is the list algorithm the Rust runs, constructor for
constructor. `OwnedInstance.transport` carries every obligation over, given that `stepL` agrees
with the set-based `step` on the traces that arise (`stepL_eq`), so Claim 1 holds for the list
instance too (`solve_sound_L`, `hcol_sound_L`). This is the model the refinement of the Rust
targets.
-/

namespace Formalism.HCol
open Formalism

/-- A trace as the code keeps it: pairs sorted by variable. -/
abbrev TauL := List (Var × Val)

/-! ## Sorted lists of pairs with distinct keys -/

/-- Strictly increasing keys. -/
abbrev KeySorted (l : TauL) : Prop := l.Pairwise fun p q => p.1 < q.1

theorem KeySorted.nodup {l : TauL} (h : KeySorted l) : l.Nodup :=
  h.imp fun hlt => fun heq => absurd (heq ▸ hlt) (lt_irrefl _)

/-- Two key-sorted lists with the same members are equal. -/
theorem eq_of_keySorted_of_mem_iff :
    ∀ {l₁ l₂ : TauL}, KeySorted l₁ → KeySorted l₂ → (∀ p, p ∈ l₁ ↔ p ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], q :: _, _, _, h => absurd ((h q).mpr (List.mem_cons_self ..)) (fun h' => nomatch h')
  | p :: _, [], _, _, h => absurd ((h p).mp (List.mem_cons_self ..)) (fun h' => nomatch h')
  | p :: l₁, q :: l₂, h₁, h₂, h => by
    have h₁ := List.pairwise_cons.mp h₁
    have h₂ := List.pairwise_cons.mp h₂
    have hpq : p = q := by
      have hp := (h p).mp (List.mem_cons_self ..)
      have hq := (h q).mpr (List.mem_cons_self ..)
      rw [List.mem_cons] at hp hq
      rcases hp with hp | hp
      · exact hp
      · rcases hq with hq | hq
        · exact hq.symm
        · exact absurd ((h₂.1 p hp).trans (h₁.1 q hq)) (lt_irrefl _)
    subst hpq
    rw [eq_of_keySorted_of_mem_iff h₁.2 h₂.2]
    intro r
    constructor
    · intro hr
      have := (h r).mp (List.mem_cons_of_mem _ hr)
      rw [List.mem_cons] at this
      rcases this with rfl | this
      · exact absurd (h₁.1 r hr) (lt_irrefl _)
      · exact this
    · intro hr
      have := (h r).mpr (List.mem_cons_of_mem _ hr)
      rw [List.mem_cons] at this
      rcases this with rfl | this
      · exact absurd (h₂.1 r hr) (lt_irrefl _)
      · exact this

/-- `insert_sorted`: `(v, d)` goes before the first pair whose variable is above `v`, else at
    the end. -/
def insertSorted : TauL → Var → Val → TauL
  | [], v, d => [(v, d)]
  | p :: rest, v, d => if v < p.1 then (v, d) :: p :: rest else p :: insertSorted rest v d

theorem mem_insertSorted {v : Var} {d : Val} {q : Var × Val} :
    ∀ {l : TauL}, q ∈ insertSorted l v d ↔ q = (v, d) ∨ q ∈ l
  | [] => by
    rw [insertSorted, List.mem_singleton]
    exact ⟨Or.inl, fun h => h.elim id fun h => nomatch h⟩
  | p :: rest => by
    rw [insertSorted]
    split
    · rw [List.mem_cons]
    · rw [List.mem_cons, mem_insertSorted, List.mem_cons]
      tauto

theorem insertSorted_keySorted {v : Var} {d : Val} :
    ∀ {l : TauL}, KeySorted l → (∀ p ∈ l, p.1 ≠ v) → KeySorted (insertSorted l v d)
  | [], _, _ => List.pairwise_singleton _ _
  | p :: rest, h, hv => by
    have h := List.pairwise_cons.mp h
    rw [insertSorted]
    split
    · rename_i hlt
      refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr h⟩
      intro q hq
      rw [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hlt
      · exact hlt.trans (h.1 q hq)
    · rename_i hge
      refine List.pairwise_cons.mpr
        ⟨?_, insertSorted_keySorted h.2 fun q hq => hv q (List.mem_cons_of_mem _ hq)⟩
      intro q hq
      rw [mem_insertSorted] at hq
      rcases hq with rfl | hq
      · exact lt_of_le_of_ne (not_lt.mp hge) (hv p (List.mem_cons_self ..))
      · exact h.1 q hq

/-- The sorted list of an assignment's pairs: its pairs inserted one by one. -/
noncomputable def toSorted (g : Assign) : TauL :=
  g.1.toList.foldr (fun p acc => insertSorted acc p.1 p.2) []

theorem mem_foldr_insertSorted {q : Var × Val} :
    ∀ l : List (Var × Val), q ∈ l.foldr (fun p acc => insertSorted acc p.1 p.2) [] ↔ q ∈ l
  | [] => Iff.rfl
  | p :: rest => by
    rw [List.foldr_cons, mem_insertSorted, List.mem_cons, mem_foldr_insertSorted rest]

theorem mem_toSorted {g : Assign} {p : Var × Val} : p ∈ toSorted g ↔ p ∈ g.1 := by
  rw [toSorted, mem_foldr_insertSorted, Finset.mem_toList]

theorem keySorted_foldr_insertSorted {g : Assign} :
    ∀ l : List (Var × Val), l.Nodup → (∀ p ∈ l, p ∈ g.1) →
      KeySorted (l.foldr (fun p acc => insertSorted acc p.1 p.2) [])
  | [], _, _ => List.Pairwise.nil
  | p :: rest, hnd, hmem => by
    rw [List.foldr_cons]
    have hnd' := List.nodup_cons.mp hnd
    apply insertSorted_keySorted
      (keySorted_foldr_insertSorted rest hnd'.2 fun q hq => hmem q (List.mem_cons_of_mem _ hq))
    intro q hq hqp
    rw [mem_foldr_insertSorted] at hq
    have : q = p := g.2 q (hmem q (List.mem_cons_of_mem _ hq)) p (hmem p (List.mem_cons_self ..)) hqp
    subst this
    exact hnd'.1 hq

theorem toSorted_keySorted (g : Assign) : KeySorted (toSorted g) :=
  keySorted_foldr_insertSorted _ (Finset.nodup_toList _) fun p hp => Finset.mem_toList.mp hp

theorem toSorted_nodup (g : Assign) : (toSorted g).Nodup := KeySorted.nodup (toSorted_keySorted g)

theorem toSorted_injective : Function.Injective toSorted := by
  intro g g' h
  apply Subtype.ext
  ext p
  rw [← mem_toSorted, ← mem_toSorted, h]

theorem toSorted_eq_iff {g g' : Assign} : toSorted g = toSorted g' ↔ g = g' :=
  ⟨fun h => toSorted_injective h, fun h => h ▸ rfl⟩

theorem toSorted_empty : toSorted Assign.empty = [] := by
  rw [toSorted, show Assign.empty.1 = (∅ : Finset (Var × Val)) from rfl, Finset.toList_empty]
  rfl

theorem toSorted_eq_nil_iff {g : Assign} : toSorted g = [] ↔ g = Assign.empty := by
  constructor
  · intro h
    apply Subtype.ext
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have := mem_toSorted.mpr hp
    rw [h] at this
    exact absurd this (fun h' => nomatch h')
  · rintro rfl
    exact toSorted_empty

/-! ## The list algorithms of `hcol.rs` -/

/-- The inserted pair's position depends on the keys only, so the colour is recoverable. -/
theorem insertSorted_inj {v : Var} {d d' : Val} :
    ∀ {l : TauL}, insertSorted l v d = insertSorted l v d' → d = d'
  | [], h => by
    rw [insertSorted, insertSorted] at h
    exact (Prod.mk.inj (List.cons.inj h).1).2
  | p :: rest, h => by
    rw [insertSorted, insertSorted] at h
    by_cases hlt : v < p.1
    · rw [if_pos hlt, if_pos hlt] at h
      exact (Prod.mk.inj (List.cons.inj h).1).2
    · rw [if_neg hlt, if_neg hlt] at h
      exact insertSorted_inj (List.cons.inj h).2

/-- `remove`. -/
def remove (f : TauL) (v : Var) : TauL := f.filter fun p => decide (p.1 ≠ v)

theorem mem_remove {f : TauL} {v : Var} {q : Var × Val} : q ∈ remove f v ↔ q ∈ f ∧ q.1 ≠ v := by
  rw [remove, List.mem_filter, decide_eq_true_iff]

theorem remove_keySorted {f : TauL} (h : KeySorted f) (v : Var) : KeySorted (remove f v) :=
  List.Pairwise.sublist List.filter_sublist h

/-- `consistent`, over a list. -/
def consistentL (P : Graphs) (f : TauL) (v : Var) (d : Val) : Bool :=
  decide ((∀ p ∈ f, P.adjG p.1 v = true → P.adjH p.2 d = true) ∧
    (P.adjG v v = true → P.adjH d d = true))

theorem consistentL_toSorted (P : Graphs) (f : Assign) (v : Var) (d : Val) :
    consistentL P (toSorted f) v d = consistent P f v d := by
  unfold consistentL consistent
  rw [decide_eq_decide]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => h1 p (mem_toSorted.mpr hp), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => h1 p (mem_toSorted.mp hp), h2⟩

/-- `HColoring::step`, on list traces. -/
def stepL (P : Graphs) (op : HOp) (taus : List TauL) : List (TauL × List (Var × Val)) :=
  match op with
  | .leaf => [([], [])]
  | .intro v o =>
    match taus with
    | f :: _ =>
      (List.range P.nH).filterMap fun d =>
        if consistentL P f v d = true then
          some (insertSorted f v d, if o then [(v, d)] else []) else none
    | [] => []
  | .forget v =>
    match taus with
    | f :: _ => [(remove f v, [])]
    | [] => []
  | .join =>
    match taus with
    | f1 :: f2 :: _ => if f1 = f2 then [(f1, [])] else []
    | _ => []

/-- `accept`. -/
def acceptL (t : TauL) : Bool := decide (t = [])

/-! ## The list algorithms agree with the set-based `step` on sorted traces -/

theorem toSorted_join_single {f : Assign} {v : Var} {d : Val} (hv : v ∉ f.dom) :
    toSorted ((Assign.single v d).join f) = insertSorted (toSorted f) v d := by
  apply eq_of_keySorted_of_mem_iff (toSorted_keySorted _)
  · apply insertSorted_keySorted (toSorted_keySorted f)
    intro p hp hpv
    apply hv
    rw [← hpv]
    exact Assign.fst_mem_dom (mem_toSorted.mp hp)
  · intro q
    rw [mem_toSorted, mem_insertSorted, mem_toSorted, Assign.mem_join_val, mem_single,
      Assign.single_dom, Finset.mem_singleton]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨h, fun hq => hv (by rw [← hq]; exact Assign.fst_mem_dom h)⟩

theorem toSorted_restrict_erase (f : Assign) (v : Var) :
    toSorted (f.restrict (f.dom.erase v)) = remove (toSorted f) v := by
  apply eq_of_keySorted_of_mem_iff (toSorted_keySorted _) (remove_keySorted (toSorted_keySorted f) v)
  intro q
  rw [mem_toSorted, mem_remove, mem_toSorted, Assign.mem_restrict_val, Finset.mem_erase]
  constructor
  · rintro ⟨hq, hne, _⟩
    exact ⟨hq, hne⟩
  · rintro ⟨hq, hne⟩
    exact ⟨hq, hne, Assign.fst_mem_dom hq⟩

/-- `stepL` on the sorted traces of the children's candidates is `step` read through
    `toSorted`. -/
theorem stepL_eq (P : Graphs) (op : HOp) (cs : List (Node HOp)) (gs : List Assign)
    (hwf : WF (.mk op cs)) (hgs : List.Forall₂ (fun g c => g ∈ cands P c) gs cs) :
    stepL P op ((List.zipWith trace cs gs).map toSorted) =
      (step P op (List.zipWith trace cs gs)).map fun o => (toSorted o.1, o.2) := by
  cases hwf with
  | leaf =>
    rw [List.forall₂_nil_right_iff.mp hgs]
    show [([], [])] = [(toSorted Assign.empty, ([] : List (Var × Val)))]
    rw [toSorted_empty]
  | @intro v o c hc hv =>
    obtain ⟨g', rfl, hg'⟩ := forall₂_single hgs
    have hv' : v ∉ (g'.restrict (bag c)).dom := by
      rw [Assign.restrict_dom, (mem_cands.mp hg').2.1]
      exact fun h => hv (Finset.mem_inter.mp h).1
    show (List.range P.nH).filterMap _ = ((List.range P.nH).filterMap _).map _
    rw [List.map_filterMap]
    congr 1
    funext d
    show (if consistentL P (toSorted (g'.restrict (bag c))) v d = true then
        some (insertSorted (toSorted (g'.restrict (bag c))) v d, if o then [(v, d)] else [])
        else none) = _
    rw [consistentL_toSorted]
    by_cases hcons : consistent P (g'.restrict (bag c)) v d = true
    · simp only [hcons, ↓reduceIte, Option.map, toSorted_join_single hv']
    · simp only [hcons, ↓reduceIte, Option.map]
  | @forget v c _ _ _ =>
    obtain ⟨g', rfl, _⟩ := forall₂_single hgs
    show [(remove (toSorted (g'.restrict (bag c))) v, ([] : List (Var × Val)))] =
      [(toSorted ((g'.restrict (bag c)).restrict ((g'.restrict (bag c)).dom.erase v)),
        ([] : List (Var × Val)))]
    rw [toSorted_restrict_erase]
  | @join a b _ _ _ _ _ =>
    obtain ⟨g1, g2, rfl, _, _⟩ := forall₂_pair hgs
    show (if toSorted (g1.restrict (bag a)) = toSorted (g2.restrict (bag b)) then
        [(toSorted (g1.restrict (bag a)), ([] : List (Var × Val)))] else []) =
      (if g1.restrict (bag a) = g2.restrict (bag b) then
        [(g1.restrict (bag a), ([] : List (Var × Val)))] else []).map
        fun o => (toSorted o.1, o.2)
    by_cases h : g1.restrict (bag a) = g2.restrict (bag b)
    · rw [if_pos (toSorted_eq_iff.mpr h), if_pos h, List.map_cons, List.map_nil]
    · rw [if_neg (fun h' => h (toSorted_eq_iff.mp h')), if_neg h, List.map_nil]

theorem acceptL_toSorted (τ : Assign) : acceptL (toSorted τ) = decide (τ = Assign.empty) := by
  unfold acceptL
  rw [decide_eq_decide]
  exact toSorted_eq_nil_iff

theorem stepL_leaves (P : Graphs) (op : HOp) (taus : List TauL) :
    ∀ out ∈ stepL P op taus,
      (out.2.map Prod.fst).Nodup ∧ (out.2.map Prod.fst).toFinset = opOwned op := by
  intro out hout
  cases op with
  | leaf =>
    have h : out ∈ [(([] : TauL), ([] : List (Var × Val)))] := hout
    rw [List.mem_singleton] at h
    subst h
    exact ⟨List.nodup_nil, by simp [opOwned]⟩
  | intro v o =>
    cases taus with
    | nil =>
      have h : out ∈ ([] : List (TauL × List (Var × Val))) := hout
      exact nomatch h
    | cons f rest =>
      have h : out ∈ (List.range P.nH).filterMap _ := hout
      rw [List.mem_filterMap] at h
      obtain ⟨d, _, hd⟩ := h
      rw [Option.ite_none_right_eq_some] at hd
      rw [← Option.some.inj hd.2]
      cases o with
      | true => exact ⟨List.nodup_singleton _, by simp [opOwned]⟩
      | false => exact ⟨List.nodup_nil, by simp [opOwned]⟩
  | forget v =>
    cases taus with
    | nil =>
      have h : out ∈ ([] : List (TauL × List (Var × Val))) := hout
      exact nomatch h
    | cons f rest =>
      have h : out ∈ [(remove f v, ([] : List (Var × Val)))] := hout
      rw [List.mem_singleton] at h
      subst h
      exact ⟨List.nodup_nil, by simp [opOwned]⟩
  | join =>
    cases taus with
    | nil =>
      have h : out ∈ ([] : List (TauL × List (Var × Val))) := hout
      exact nomatch h
    | cons f1 rest =>
      cases rest with
      | nil =>
        have h : out ∈ ([] : List (TauL × List (Var × Val))) := hout
        exact nomatch h
      | cons f2 rest' =>
        have h : out ∈ (if f1 = f2 then [(f1, ([] : List (Var × Val)))] else []) := hout
        split at h
        · rw [List.mem_singleton] at h
          subst h
          exact ⟨List.nodup_nil, by simp [opOwned]⟩
        · exact nomatch h

theorem stepL_nodup (P : Graphs) (op : HOp) (taus : List TauL) :
    (stepL P op taus).Pairwise fun out out' =>
      out.1 = out'.1 → Assign.ofList out.2 ≠ Assign.ofList out'.2 := by
  cases op with
  | leaf => exact List.pairwise_singleton _ _
  | intro v o =>
    cases taus with
    | nil => exact List.Pairwise.nil
    | cons f rest =>
      show ((List.range P.nH).filterMap _).Pairwise _
      rw [List.pairwise_filterMap]
      refine List.Pairwise.imp ?_ List.nodup_range
      intro d d' hne b hb b' hb' hτ
      exfalso
      try dsimp only at hb hb'
      try rw [Option.mem_def] at hb hb'
      rw [Option.ite_none_right_eq_some] at hb hb'
      have hb2 := Option.some.inj hb.2
      have hb2' := Option.some.inj hb'.2
      have hτ' : insertSorted f v d = insertSorted f v d' := by
        rw [← hb2, ← hb2'] at hτ
        exact hτ
      exact hne (insertSorted_inj hτ')
  | forget v =>
    cases taus with
    | nil => exact List.Pairwise.nil
    | cons f rest => exact List.pairwise_singleton _ _
  | join =>
    cases taus with
    | nil => exact List.Pairwise.nil
    | cons f1 rest =>
      cases rest with
      | nil => exact List.Pairwise.nil
      | cons f2 rest' =>
        show (if f1 = f2 then [(f1, [])] else []).Pairwise _
        split
        · exact List.pairwise_singleton _ _
        · exact List.Pairwise.nil

/-- The H-colouring instance with list traces: `inst P` read through `toSorted`, run by the
    Rust's list algorithms. -/
noncomputable def instL (P : Graphs) : OwnedInstance HOp TauL :=
  (inst P).transport toSorted toSorted_injective (stepL P) acceptL (stepL_eq P)
    acceptL_toSorted (stepL_leaves P) (stepL_nodup P)

theorem instL_step (P : Graphs) : (instL P).step = stepL P := rfl
theorem instL_accept (P : Graphs) : (instL P).accept = acceptL := rfl
theorem instL_cands (P : Graphs) : (instL P).cands = cands P := rfl
theorem instL_trace (P : Graphs) (n : Node HOp) (g : Assign) :
    (instL P).trace n g = toSorted (g.restrict (bag n)) := rfl

/-- Claim 1 for the list instance: at a root with an empty bag, the DP's expression denotes
    exactly the candidates. -/
theorem solve_sound_L (P : Graphs) {n : Node HOp} (hwf : WF n) (hroot : bag n = ∅) :
    Sem ((instL P).toTraced.solve n) (cands P n) := by
  have h := (instL P).solve_sound hwf
  have hset : (((instL P).cands n).filter fun g => (instL P).accept ((instL P).trace n g) = true).image
      (fun g => g.restrict ((instL P).owned n)) = cands P n := by
    ext x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : g ∈ cands P n := (Finset.mem_filter.mp hg).1
      show g.restrict (owned n) ∈ cands P n
      rw [restrict_owned_eq hwf hroot hg']
      exact hg'
    · intro hx
      refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, restrict_owned_eq hwf hroot hx⟩
      show acceptL (toSorted (x.restrict (bag n))) = true
      rw [acceptL_toSorted, decide_eq_true_iff, hroot]
      exact restrict_empty_set x
  rw [hset] at h
  exact h

/-- Claim 1 for H-colouring, list traces: the `H`-colourings of `G`. -/
theorem hcol_sound_L (P : Graphs) {n : Node HOp} (hwf : WF n) (hroot : bag n = ∅)
    (hcov : ∀ u ∈ desc n, ∀ w ∈ desc n, P.adjG u w = true →
      (u, w) ∈ covered P n ∨ (w, u) ∈ covered P n)
    (hsymm : ∀ c d, P.adjH c d = P.adjH d c) :
    Sem ((instL P).toTraced.solve n) (Hom P (desc n)) := by
  rw [← cands_eq_hom hwf hcov hsymm]
  exact solve_sound_L P hwf hroot

end Formalism.HCol
