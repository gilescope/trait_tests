import FormalismVerify.SpecOwned

/-!
# H-colouring over a nice tree decomposition, as an `OwnedInstance`

The model of `instances/hcol.rs`. A construction is a nice tree decomposition of `G` read as a
tree of `Leaf`, `Introduce v`, `Forget v` and `Join` nodes; a candidate at a node is a colouring
of the vertices introduced in its subtree (`desc`) that respects every edge of `G` checked so far
(`covered`: the edges between a vertex and the bag at its introduction); the trace is the
colouring of the bag; a node owns the vertices whose owning `Introduce` is in its subtree
(`owned`). `WF` is the shape of a nice tree decomposition: a vertex is introduced once per
branch, forgotten only from the bag and only by the branch that owns it, and the two sides of a
`Join` have the same bag and meet only in it. Then `inst P` is an `OwnedInstance`, so Claim 1
holds (`solve_sound`): at a root with an empty bag the DP's expression denotes exactly the
candidates, and when the checked edges are all of `G`'s edges (`Lemma 2`, validated by the
Rust's `NiceTd::new`) those are the `H`-colourings of `G` (`hcol_sound`).
-/

namespace Formalism.HCol
open Formalism Formalism.Traced

/-- The input: `G` on variables, `H` on the colours `0 .. nH-1`, both as adjacency predicates
    (loops allowed). -/
structure Graphs where
  adjG : Var → Var → Bool
  adjH : Val → Val → Bool
  nH : ℕ

/-- Nodes of a nice tree decomposition (`instances/hcol.rs`: `Op`). -/
inductive HOp
  | leaf
  | intro (v : Var) (owner : Bool)
  | forget (v : Var)
  | join
  deriving DecidableEq

/-! ## The tree's data: bag, variables, owned variables, checked edges -/

mutual
/-- The bag at a node. -/
def bag : Node HOp → Finset Var
  | .mk .leaf _ => ∅
  | .mk (.intro v _) cs => insert v ((bagList cs).headD ∅)
  | .mk (.forget v) cs => ((bagList cs).headD ∅).erase v
  | .mk .join cs => (bagList cs).headD ∅
def bagList : List (Node HOp) → List (Finset Var)
  | [] => []
  | c :: cs => bag c :: bagList cs
end

mutual
/-- The vertices introduced in a subtree. -/
def desc : Node HOp → Finset Var
  | .mk .leaf _ => ∅
  | .mk (.intro v _) cs => insert v ((descList cs).headD ∅)
  | .mk (.forget _) cs => (descList cs).headD ∅
  | .mk .join cs => (descList cs).foldr (· ∪ ·) ∅
def descList : List (Node HOp) → List (Finset Var)
  | [] => []
  | c :: cs => desc c :: descList cs
end

/-- The vertex an operation owns: the one an owning `Introduce` introduces. -/
def opOwned : HOp → Finset Var
  | .intro v o => if o then {v} else ∅
  | _ => ∅

mutual
/-- The vertices a subtree owns. -/
def owned : Node HOp → Finset Var
  | .mk op cs => opOwned op ∪ (ownedList cs).foldr (· ∪ ·) ∅
def ownedList : List (Node HOp) → List (Finset Var)
  | [] => []
  | c :: cs => owned c :: ownedList cs
end

/-- The edges of `G` between the bag `B` and a new vertex `v`, as `(old, new)`, and `v`'s loop. -/
def newEdges (P : Graphs) (B : Finset Var) (v : Var) : Finset (Var × Var) :=
  (B.filter fun u => P.adjG u v = true).image (fun u => (u, v)) ∪
    (if P.adjG v v = true then {(v, v)} else ∅)

mutual
/-- The edges of `G` checked in a subtree. -/
def covered (P : Graphs) : Node HOp → Finset (Var × Var)
  | .mk .leaf _ => ∅
  | .mk (.intro v _) cs => (coveredList P cs).headD ∅ ∪ newEdges P ((bagList cs).headD ∅) v
  | .mk (.forget _) cs => (coveredList P cs).headD ∅
  | .mk .join cs => (coveredList P cs).foldr (· ∪ ·) ∅
def coveredList (P : Graphs) : List (Node HOp) → List (Finset (Var × Var))
  | [] => []
  | c :: cs => covered P c :: coveredList P cs
end

theorem bag_leaf : bag (.mk .leaf []) = ∅ := by simp [bag]
theorem bag_intro (v : Var) (o : Bool) (c : Node HOp) :
    bag (.mk (.intro v o) [c]) = insert v (bag c) := by simp [bag, bagList]
theorem bag_forget (v : Var) (c : Node HOp) : bag (.mk (.forget v) [c]) = (bag c).erase v := by
  simp [bag, bagList]
theorem bag_join (a b : Node HOp) : bag (.mk .join [a, b]) = bag a := by simp [bag, bagList]

theorem desc_leaf : desc (.mk .leaf []) = ∅ := by simp [desc]
theorem desc_intro (v : Var) (o : Bool) (c : Node HOp) :
    desc (.mk (.intro v o) [c]) = insert v (desc c) := by simp [desc, descList]
theorem desc_forget (v : Var) (c : Node HOp) : desc (.mk (.forget v) [c]) = desc c := by
  simp [desc, descList]
theorem desc_join (a b : Node HOp) : desc (.mk .join [a, b]) = desc a ∪ desc b := by
  simp [desc, descList]

theorem ownedList_eq_map : ∀ cs : List (Node HOp), ownedList cs = cs.map owned
  | [] => rfl
  | c :: cs => by rw [ownedList, List.map_cons, ownedList_eq_map cs]

theorem owned_mk (op : HOp) (cs : List (Node HOp)) :
    owned (.mk op cs) = opOwned op ∪ (cs.map owned).foldr (· ∪ ·) ∅ := by
  rw [owned, ownedList_eq_map]

theorem owned_leaf : owned (.mk .leaf []) = ∅ := by simp [owned, ownedList, opOwned]
theorem owned_intro (v : Var) (o : Bool) (c : Node HOp) :
    owned (.mk (.intro v o) [c]) = (if o then {v} else ∅) ∪ owned c := by
  simp [owned, ownedList, opOwned]
theorem owned_forget (v : Var) (c : Node HOp) : owned (.mk (.forget v) [c]) = owned c := by
  simp [owned, ownedList, opOwned]
theorem owned_join (a b : Node HOp) : owned (.mk .join [a, b]) = owned a ∪ owned b := by
  simp [owned, ownedList, opOwned]

theorem covered_leaf (P : Graphs) : covered P (.mk .leaf []) = ∅ := by simp [covered]
theorem covered_intro (P : Graphs) (v : Var) (o : Bool) (c : Node HOp) :
    covered P (.mk (.intro v o) [c]) = covered P c ∪ newEdges P (bag c) v := by
  simp [covered, coveredList, bagList]
theorem covered_forget (P : Graphs) (v : Var) (c : Node HOp) :
    covered P (.mk (.forget v) [c]) = covered P c := by simp [covered, coveredList]
theorem covered_join (P : Graphs) (a b : Node HOp) :
    covered P (.mk .join [a, b]) = covered P a ∪ covered P b := by simp [covered, coveredList]

theorem mem_newEdges {P : Graphs} {B : Finset Var} {v : Var} {e : Var × Var} :
    e ∈ newEdges P B v ↔
      (e.1 ∈ B ∧ P.adjG e.1 v = true ∧ e.2 = v) ∨ (e = (v, v) ∧ P.adjG v v = true) := by
  unfold newEdges
  rw [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨u, hu, rfl⟩ | h)
    · rw [Finset.mem_filter] at hu
      exact Or.inl ⟨hu.1, hu.2, rfl⟩
    · right
      split at h
      · exact ⟨Finset.mem_singleton.mp h, by assumption⟩
      · exact absurd h (Finset.notMem_empty _)
  · rintro (⟨h1, h2, h3⟩ | ⟨rfl, h⟩)
    · left
      exact ⟨e.1, Finset.mem_filter.mpr ⟨h1, h2⟩, Prod.ext rfl h3.symm⟩
    · right
      rw [if_pos h]
      exact Finset.mem_singleton_self _

/-! ## Well-formed constructions: nice tree decompositions -/

/-- The shape of a nice tree decomposition. `forget` asks that the branch forgetting a vertex
    owns it: in a decomposition that passes the Rust's `NiceTd::new` the owner cannot be an
    ancestor (`IntroduceAlreadyPresent`) nor in another branch (that branch would meet this one
    outside the `Join`'s bag), so this is what validation implies. -/
inductive WF : Node HOp → Prop
  | leaf : WF (.mk .leaf [])
  | intro {v : Var} {o : Bool} {c : Node HOp} : WF c → v ∉ desc c → WF (.mk (.intro v o) [c])
  | forget {v : Var} {c : Node HOp} : WF c → v ∈ bag c → v ∈ owned c → WF (.mk (.forget v) [c])
  | join {a b : Node HOp} : WF a → WF b → bag a = bag b → desc a ∩ desc b ⊆ bag a →
      Disjoint (owned a) (owned b) → WF (.mk .join [a, b])

theorem wf_children (op : HOp) (cs : List (Node HOp)) (h : WF (.mk op cs)) :
    ∀ c ∈ cs, WF c := by
  intro c hc
  cases h with
  | leaf => nomatch hc
  | intro hc' _ =>
    rw [List.mem_singleton] at hc
    subst hc
    exact hc'
  | forget hc' _ _ =>
    rw [List.mem_singleton] at hc
    subst hc
    exact hc'
  | join ha hb _ _ _ =>
    rw [List.mem_cons, List.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact ha
    · exact hb

theorem bag_sub_desc {n : Node HOp} (h : WF n) : bag n ⊆ desc n := by
  induction h with
  | leaf =>
    intro x hx
    rw [bag_leaf] at hx
    exact absurd hx (Finset.notMem_empty _)
  | @intro v o c _ _ ih =>
    rw [bag_intro, desc_intro]
    exact Finset.insert_subset_insert v ih
  | @forget v c _ _ _ ih =>
    rw [bag_forget, desc_forget]
    exact (Finset.erase_subset v _).trans ih
  | @join a b _ _ _ _ _ iha _ =>
    rw [bag_join, desc_join]
    exact iha.trans Finset.subset_union_left

theorem owned_sub_desc {n : Node HOp} (h : WF n) : owned n ⊆ desc n := by
  induction h with
  | leaf =>
    intro x hx
    rw [owned_leaf] at hx
    exact absurd hx (Finset.notMem_empty _)
  | @intro v o c _ _ ih =>
    rw [owned_intro, desc_intro]
    apply Finset.union_subset _ (ih.trans (Finset.subset_insert _ _))
    split
    · rw [Finset.singleton_subset_iff]
      exact Finset.mem_insert_self _ _
    · exact Finset.empty_subset _
  | @forget v c _ _ _ ih =>
    rw [owned_forget, desc_forget]
    exact ih
  | @join a b _ _ _ _ _ iha ihb =>
    rw [owned_join, desc_join]
    exact Finset.union_subset_union iha ihb

/-- Every vertex of a subtree is owned by it or still in its bag. -/
theorem desc_sub_owned_union_bag {n : Node HOp} (h : WF n) : desc n ⊆ owned n ∪ bag n := by
  induction h with
  | leaf => rw [desc_leaf]; exact Finset.empty_subset _
  | @intro v o c _ _ ih =>
    rw [desc_intro, owned_intro, bag_intro]
    intro x hx
    rw [Finset.mem_insert] at hx
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_insert]
    rcases hx with rfl | hx
    · exact Or.inr (Or.inl rfl)
    · rcases Finset.mem_union.mp (ih hx) with hx | hx
      · exact Or.inl (Or.inr hx)
      · exact Or.inr (Or.inr hx)
  | @forget v c _ _ hvo ih =>
    rw [desc_forget, owned_forget, bag_forget]
    intro x hx
    rw [Finset.mem_union, Finset.mem_erase]
    rcases Finset.mem_union.mp (ih hx) with hx | hx
    · exact Or.inl hx
    · by_cases hxv : x = v
      · subst hxv
        exact Or.inl hvo
      · exact Or.inr ⟨hxv, hx⟩
  | @join a b _ _ hbag _ _ iha ihb =>
    rw [desc_join, owned_join, bag_join]
    intro x hx
    rw [Finset.mem_union, Finset.mem_union]
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp (iha hx) with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx
    · rcases Finset.mem_union.mp (ihb hx) with hx | hx
      · exact Or.inl (Or.inr hx)
      · rw [hbag]
        exact Or.inr hx

/-- Checked edges are between vertices of the subtree. -/
theorem covered_sub_desc {P : Graphs} {n : Node HOp} (h : WF n) :
    ∀ e ∈ covered P n, e.1 ∈ desc n ∧ e.2 ∈ desc n := by
  induction h with
  | leaf =>
    rw [covered_leaf]
    intro e he
    exact absurd he (Finset.notMem_empty _)
  | @intro v o c hc _ ih =>
    rw [covered_intro, desc_intro]
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact ⟨Finset.mem_insert_of_mem (ih e he).1, Finset.mem_insert_of_mem (ih e he).2⟩
    · rcases mem_newEdges.mp he with ⟨h1, _, h3⟩ | ⟨rfl, _⟩
      · rw [h3]
        exact ⟨Finset.mem_insert_of_mem (bag_sub_desc hc h1), Finset.mem_insert_self _ _⟩
      · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
  | @forget v c _ _ _ ih =>
    rw [covered_forget, desc_forget]
    exact ih
  | @join a b _ _ _ _ _ iha ihb =>
    rw [covered_join, desc_join]
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact ⟨Finset.mem_union_left _ (iha e he).1, Finset.mem_union_left _ (iha e he).2⟩
    · exact ⟨Finset.mem_union_right _ (ihb e he).1, Finset.mem_union_right _ (ihb e he).2⟩

/-- Checked edges are edges of `G`. -/
theorem covered_adj {P : Graphs} {n : Node HOp} (h : WF n) :
    ∀ e ∈ covered P n, P.adjG e.1 e.2 = true := by
  induction h with
  | leaf =>
    rw [covered_leaf]
    intro e he
    exact absurd he (Finset.notMem_empty _)
  | @intro v o c _ _ ih =>
    rw [covered_intro]
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact ih e he
    · rcases mem_newEdges.mp he with ⟨_, h2, h3⟩ | ⟨rfl, h⟩
      · rw [h3]
        exact h2
      · exact h
  | @forget v c _ _ _ ih =>
    rw [covered_forget]
    exact ih
  | @join a b _ _ _ _ _ iha ihb =>
    rw [covered_join]
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact iha e he
    · exact ihb e he

/-! ## Assignments: a few more facts -/

theorem eq_of_mem_of_mem {g : Assign} {p q : Var × Val} (hp : p ∈ g.1) (hq : q ∈ g.1)
    (h : p.1 = q.1) : p = q := g.2 p hp q hq h

theorem exists_mem_of_mem_dom {g : Assign} {x : Var} (hx : x ∈ g.dom) : ∃ p ∈ g.1, p.1 = x :=
  Finset.mem_image.mp hx

theorem mem_single {v : Var} {d : Val} {p : Var × Val} : p ∈ (Assign.single v d).1 ↔ p = (v, d) :=
  Finset.mem_singleton

theorem restrict_restrict (f : Assign) (A B : Finset Var) :
    (f.restrict A).restrict B = f.restrict (A ∩ B) := by
  apply Subtype.ext
  ext p
  rw [Assign.mem_restrict_val, Assign.mem_restrict_val, Assign.mem_restrict_val, Finset.mem_inter,
    and_assoc]

theorem restrict_of_dom_sub {f : Assign} {A : Finset Var} (h : f.dom ⊆ A) : f.restrict A = f := by
  apply Subtype.ext
  ext p
  rw [Assign.mem_restrict_val]
  exact ⟨fun hp => hp.1, fun hp => ⟨hp, h (Assign.fst_mem_dom hp)⟩⟩

theorem join_of_dom_sub {f g : Assign} (h : g.dom ⊆ f.dom) : f.join g = f := by
  apply Subtype.ext
  ext p
  rw [Assign.mem_join_val]
  exact ⟨fun hp => hp.elim id fun hp => absurd (h (Assign.fst_mem_dom hp.1)) hp.2, Or.inl⟩

theorem restrict_empty_set (f : Assign) : f.restrict ∅ = Assign.empty := by
  apply Subtype.ext
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  exact Finset.notMem_empty _ (Assign.mem_restrict_val.mp hp).2

theorem eq_empty_of_dom_eq_empty {g : Assign} (h : g.dom = ∅) : g = Assign.empty := by
  apply Subtype.ext
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  have := Assign.fst_mem_dom hp
  rw [h] at this
  exact Finset.notMem_empty _ this

theorem compat_restrict (g : Assign) (A B : Finset Var) :
    Assign.Compat (g.restrict A) (g.restrict B) := by
  intro p hp q hq hpq
  exact g.2 p (Assign.mem_restrict_val.mp hp).1 q (Assign.mem_restrict_val.mp hq).1 hpq

/-- Two full colourings that agree on the bag and meet only in it are compatible. -/
theorem compat_of_restrict_eq {g1 g2 : Assign} {B : Finset Var} (hmeet : g1.dom ∩ g2.dom ⊆ B)
    (hres : g1.restrict B = g2.restrict B) : Assign.Compat g1 g2 := by
  intro p hp q hq hpq
  have hpB : p.1 ∈ B := hmeet (Finset.mem_inter.mpr ⟨Assign.fst_mem_dom hp,
    by rw [hpq]; exact Assign.fst_mem_dom hq⟩)
  have hp2 : p ∈ g2.1 := by
    have h : p ∈ (g1.restrict B).1 := Assign.mem_restrict_val.mpr ⟨hp, hpB⟩
    rw [hres, Assign.mem_restrict_val] at h
    exact h.1
  exact g2.2 p hp2 q hq hpq

theorem mem_join_left_of_mem_dom {g1 g2 : Assign} (h : Assign.Compat g1 g2) {p : Var × Val}
    (hp : p ∈ (g1.join g2).1) (hd : p.1 ∈ g1.dom) : p ∈ g1.1 := by
  rw [Assign.join_val_of_compat h, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact hp
  · obtain ⟨p', hp', hp'1⟩ := exists_mem_of_mem_dom hd
    rw [← h p' hp' p hp hp'1]
    exact hp'

theorem mem_join_right_of_mem_dom {g1 g2 : Assign} (h : Assign.Compat g1 g2) {p : Var × Val}
    (hp : p ∈ (g1.join g2).1) (hd : p.1 ∈ g2.dom) : p ∈ g2.1 := by
  rw [Assign.join_val_of_compat h, Finset.mem_union] at hp
  rcases hp with hp | hp
  · obtain ⟨p', hp', hp'1⟩ := exists_mem_of_mem_dom hd
    rw [h p hp p' hp' hp'1.symm]
    exact hp'
  · exact hp

theorem mem_join_single_of_ne {g : Assign} {v : Var} {d : Val} {p : Var × Val}
    (hp : p ∈ (g.join (Assign.single v d)).1) (hne : p.1 ≠ v) : p ∈ g.1 := by
  rw [Assign.mem_join_val] at hp
  rcases hp with hp | ⟨hp, _⟩
  · exact hp
  · rw [mem_single] at hp
    subst hp
    exact absurd rfl hne

theorem mem_join_single_of_eq {g : Assign} {v : Var} {d : Val} {p : Var × Val}
    (hp : p ∈ (g.join (Assign.single v d)).1) (hv : v ∉ g.dom) (hpv : p.1 = v) : p = (v, d) := by
  rw [Assign.mem_join_val] at hp
  rcases hp with hp | ⟨hp, _⟩
  · exact absurd (hpv ▸ Assign.fst_mem_dom hp) hv
  · exact mem_single.mp hp

theorem joinAll_single (g : Assign) : Assign.joinAll [g] = g := by
  show Assign.empty.join g = g
  exact Assign.empty_join g

theorem joinAll_pair (g1 g2 : Assign) : Assign.joinAll [g1, g2] = g1.join g2 := by
  show (Assign.empty.join g1).join g2 = g1.join g2
  rw [Assign.empty_join]

theorem ofList_single (v : Var) (d : Val) : Assign.ofList [(v, d)] = Assign.single v d := by
  show (Assign.single v d).join (Assign.ofList []) = _
  show (Assign.single v d).join Assign.empty = _
  exact Assign.join_empty _

/-- A full colouring extended by one new vertex, restricted to a bag that gains it. -/
theorem restrict_join_single {g : Assign} {v : Var} {d : Val} (hv : v ∉ g.dom) (B : Finset Var) :
    (g.join (Assign.single v d)).restrict (insert v B) = (Assign.single v d).join (g.restrict B) := by
  apply Assign.ext_of_dom_eq
  · rw [Assign.restrict_dom, Assign.join_dom_eq, Assign.join_dom_eq, Assign.single_dom,
      Assign.restrict_dom]
    ext x
    rw [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert,
      Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ⟨hx | rfl, hx' | hx'⟩
      · exact Or.inl hx'
      · exact Or.inr ⟨hx, hx'⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
    · rintro (rfl | ⟨hx, hx'⟩)
      · exact ⟨Or.inr rfl, Or.inl rfl⟩
      · exact ⟨Or.inl hx, Or.inr hx'⟩
  · intro p hp
    rw [Assign.mem_restrict_val, Finset.mem_insert] at hp
    obtain ⟨hp, hpv⟩ := hp
    rw [Assign.mem_join_val, mem_single, Assign.mem_restrict_val, Assign.single_dom,
      Finset.mem_singleton]
    by_cases hpv' : p.1 = v
    · exact Or.inl (mem_join_single_of_eq hp hv hpv')
    · have hpg := mem_join_single_of_ne hp hpv'
      rcases hpv with hpv | hpv
      · exact absurd hpv hpv'
      · exact Or.inr ⟨⟨hpg, hpv⟩, hpv'⟩

/-! ## The instance's executable part: `consistent`, `step`, `accept` -/

/-- `f ∪ {v ↦ d}` respects every edge of `G` between `v` and the bag `f`, and `v`'s loop. -/
def consistent (P : Graphs) (f : Assign) (v : Var) (d : Val) : Bool :=
  decide ((∀ p ∈ f.1, P.adjG p.1 v = true → P.adjH p.2 d = true) ∧
    (P.adjG v v = true → P.adjH d d = true))

theorem consistent_iff {P : Graphs} {f : Assign} {v : Var} {d : Val} :
    consistent P f v d = true ↔
      (∀ p ∈ f.1, P.adjG p.1 v = true → P.adjH p.2 d = true) ∧
        (P.adjG v v = true → P.adjH d d = true) :=
  decide_eq_true_iff

/-- `HColoring::step`. -/
def step (P : Graphs) (op : HOp) (taus : List Assign) : List (Assign × List (Var × Val)) :=
  match op with
  | .leaf => [(Assign.empty, [])]
  | .intro v o =>
    match taus with
    | f :: _ =>
      (List.range P.nH).filterMap fun d =>
        if consistent P f v d = true then
          some ((Assign.single v d).join f, if o then [(v, d)] else []) else none
    | [] => []
  | .forget v =>
    match taus with
    | f :: _ => [(f.restrict (f.dom.erase v), [])]
    | [] => []
  | .join =>
    match taus with
    | f1 :: f2 :: _ => if f1 = f2 then [(f1, [])] else []
    | _ => []

theorem step_intro_mem {P : Graphs} {v : Var} {o : Bool} {f : Assign} {rest : List Assign}
    {out : Assign × List (Var × Val)} :
    out ∈ step P (.intro v o) (f :: rest) ↔
      ∃ d, d < P.nH ∧ consistent P f v d = true ∧
        out = ((Assign.single v d).join f, if o then [(v, d)] else []) := by
  show out ∈ (List.range P.nH).filterMap _ ↔ _
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨d, hd, h⟩
    rw [List.mem_range] at hd
    rw [Option.ite_none_right_eq_some] at h
    exact ⟨d, hd, h.1, h.2.symm⟩
  · rintro ⟨d, hd, hcons, rfl⟩
    exact ⟨d, List.mem_range.mpr hd, by rw [if_pos hcons]⟩

theorem step_join_mem {P : Graphs} {f1 f2 : Assign} {rest : List Assign}
    {out : Assign × List (Var × Val)} :
    out ∈ step P .join (f1 :: f2 :: rest) ↔ f1 = f2 ∧ out = (f1, []) := by
  show out ∈ (if f1 = f2 then [(f1, [])] else []) ↔ _
  by_cases h : f1 = f2
  · rw [if_pos h, List.mem_singleton]
    exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
  · rw [if_neg h]
    exact ⟨fun h' => nomatch h', fun h' => absurd h'.1 h⟩

theorem step_leaves (P : Graphs) (op : HOp) (taus : List Assign) :
    ∀ out ∈ step P op taus,
      (out.2.map Prod.fst).Nodup ∧ (out.2.map Prod.fst).toFinset = opOwned op := by
  intro out hout
  cases op with
  | leaf =>
    have h : out ∈ [(Assign.empty, ([] : List (Var × Val)))] := hout
    rw [List.mem_singleton] at h
    subst h
    exact ⟨List.nodup_nil, by simp [opOwned]⟩
  | intro v o =>
    cases taus with
    | nil =>
      have h : out ∈ ([] : List (Assign × List (Var × Val))) := hout
      exact nomatch h
    | cons f rest =>
      obtain ⟨d, _, _, rfl⟩ := step_intro_mem.mp hout
      cases o with
      | true => exact ⟨List.nodup_singleton _, by simp [opOwned]⟩
      | false => exact ⟨List.nodup_nil, by simp [opOwned]⟩
  | forget v =>
    cases taus with
    | nil =>
      have h : out ∈ ([] : List (Assign × List (Var × Val))) := hout
      exact nomatch h
    | cons f rest =>
      have h : out ∈ [(f.restrict (f.dom.erase v), ([] : List (Var × Val)))] := hout
      rw [List.mem_singleton] at h
      subst h
      exact ⟨List.nodup_nil, by simp [opOwned]⟩
  | join =>
    cases taus with
    | nil =>
      have h : out ∈ ([] : List (Assign × List (Var × Val))) := hout
      exact nomatch h
    | cons f1 rest =>
      cases rest with
      | nil =>
        have h : out ∈ ([] : List (Assign × List (Var × Val))) := hout
        exact nomatch h
      | cons f2 rest' =>
        obtain ⟨_, rfl⟩ := step_join_mem.mp hout
        exact ⟨List.nodup_nil, by simp [opOwned]⟩

theorem step_nodup (P : Graphs) (op : HOp) (taus : List Assign) :
    (step P op taus).Pairwise fun out out' =>
      out.1 = out'.1 → Assign.ofList out.2 ≠ Assign.ofList out'.2 := by
  cases op with
  | leaf => exact List.pairwise_singleton _ _
  | intro v o =>
    cases taus with
    | nil => exact List.Pairwise.nil
    | cons f rest =>
      show ((List.range P.nH).filterMap _).Pairwise _
      rw [List.pairwise_filterMap]
      refine List.Pairwise.imp ?_ (List.nodup_range P.nH)
      intro d d' hne b hb b' hb' hτ
      exfalso
      try dsimp only at hb hb'
      rw [Option.mem_def, Option.ite_none_right_eq_some] at hb hb'
      have hτ' : (Assign.single v d).join f = (Assign.single v d').join f := by
        rw [← hb.2, ← hb'.2] at hτ
        exact hτ
      have h1 : (v, d) ∈ ((Assign.single v d).join f).1 :=
        Assign.mem_join_val.mpr (Or.inl (mem_single.mpr rfl))
      rw [hτ', Assign.mem_join_val, mem_single, Assign.single_dom, Finset.mem_singleton] at h1
      rcases h1 with h1 | ⟨_, h1⟩
      · exact hne (Prod.mk.inj h1).2
      · exact h1 rfl
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

/-! ## Candidates -/

instance : DecidablePred Functional := fun s => by unfold Functional; infer_instance

/-- All partial colourings of `D` with colours below `k`. -/
def allAssign (D : Finset Var) (k : ℕ) : Finset Assign :=
  (D ×ˢ Finset.range k).powerset.subtype Functional

theorem mem_allAssign {D : Finset Var} {k : ℕ} {g : Assign} :
    g ∈ allAssign D k ↔ ∀ p ∈ g.1, p.1 ∈ D ∧ p.2 < k := by
  unfold allAssign
  rw [Finset.mem_subtype, Finset.mem_powerset, Finset.subset_iff]
  constructor
  · intro h p hp
    have := h hp
    rw [Finset.mem_product, Finset.mem_range] at this
    exact this
  · intro h p hp
    rw [Finset.mem_product, Finset.mem_range]
    exact h p hp

/-- `g` respects the edges `E` (as `(u, w)`: the colour of `u` is adjacent in `H` to that of
    `w`). -/
def ConsistentOn (P : Graphs) (E : Finset (Var × Var)) (g : Assign) : Prop :=
  ∀ p ∈ g.1, ∀ q ∈ g.1, (p.1, q.1) ∈ E → P.adjH p.2 q.2 = true

instance (P : Graphs) (E : Finset (Var × Var)) : DecidablePred (ConsistentOn P E) := fun g => by
  unfold ConsistentOn; infer_instance

/-- The candidates at a node: colourings of its vertices respecting the edges checked in it. -/
def cands (P : Graphs) (n : Node HOp) : Finset Assign :=
  (allAssign (desc n) P.nH).filter fun g => g.dom = desc n ∧ ConsistentOn P (covered P n) g

theorem mem_cands {P : Graphs} {n : Node HOp} {g : Assign} :
    g ∈ cands P n ↔
      (∀ p ∈ g.1, p.1 ∈ desc n ∧ p.2 < P.nH) ∧ g.dom = desc n ∧ ConsistentOn P (covered P n) g := by
  rw [cands, Finset.mem_filter, mem_allAssign]

theorem consistentOn_mono {P : Graphs} {E E' : Finset (Var × Var)} (hE : E ⊆ E') {g : Assign}
    (h : ConsistentOn P E' g) : ConsistentOn P E g := by
  intro p hp q hq he
  exact h p hp q hq (hE he)

theorem consistentOn_restrict {P : Graphs} {E : Finset (Var × Var)} {g : Assign}
    (h : ConsistentOn P E g) (D : Finset Var) : ConsistentOn P E (g.restrict D) := by
  intro p hp q hq he
  exact h p (Assign.mem_restrict_val.mp hp).1 q (Assign.mem_restrict_val.mp hq).1 he

theorem cands_leaf {P : Graphs} {g : Assign} : g ∈ cands P (.mk .leaf []) ↔ g = Assign.empty := by
  rw [mem_cands, desc_leaf, covered_leaf]
  constructor
  · rintro ⟨_, hdom, _⟩
    exact eq_empty_of_dom_eq_empty hdom
  · rintro rfl
    refine ⟨fun p hp => absurd hp (Finset.notMem_empty _), Assign.empty_dom, ?_⟩
    intro p hp
    exact absurd hp (Finset.notMem_empty _)

/-- Candidates at `Introduce v`: a candidate of the child extended by a colour for `v` that is
    consistent with the bag. -/
theorem cands_intro {P : Graphs} {v : Var} {o : Bool} {c : Node HOp} (hc : WF c) (hv : v ∉ desc c)
    {g : Assign} :
    g ∈ cands P (.mk (.intro v o) [c]) ↔
      ∃ g' ∈ cands P c, ∃ d, d < P.nH ∧ consistent P (g'.restrict (bag c)) v d = true ∧
        g = g'.join (Assign.single v d) := by
  rw [mem_cands, desc_intro, covered_intro]
  constructor
  · rintro ⟨hvals, hdom, hcons⟩
    have hvdom : v ∈ g.dom := by rw [hdom]; exact Finset.mem_insert_self _ _
    obtain ⟨pv, hpv, hpv1⟩ := exists_mem_of_mem_dom hvdom
    have hdom' : (g.restrict (desc c)).dom = desc c := by
      rw [Assign.restrict_dom, hdom]
      exact Finset.inter_eq_right.mpr (Finset.subset_insert _ _)
    refine ⟨g.restrict (desc c), ?_, pv.2, (hvals pv hpv).2, ?_, ?_⟩
    · rw [mem_cands]
      refine ⟨?_, hdom', consistentOn_restrict (consistentOn_mono Finset.subset_union_left hcons) _⟩
      intro p hp
      rw [Assign.mem_restrict_val] at hp
      exact ⟨hp.2, (hvals p hp.1).2⟩
    · rw [consistent_iff]
      constructor
      · intro p hp hadj
        rw [Assign.mem_restrict_val, Assign.mem_restrict_val] at hp
        have he : (p.1, pv.1) ∈ covered P c ∪ newEdges P (bag c) v := by
          rw [hpv1]
          exact Finset.mem_union_right _ (mem_newEdges.mpr (Or.inl ⟨hp.2, hadj, rfl⟩))
        exact hcons p hp.1.1 pv hpv he
      · intro hloop
        have he : (pv.1, pv.1) ∈ covered P c ∪ newEdges P (bag c) v := by
          rw [hpv1]
          exact Finset.mem_union_right _ (mem_newEdges.mpr (Or.inr ⟨rfl, hloop⟩))
        exact hcons pv hpv pv hpv he
    · apply Assign.ext_of_dom_eq
      · rw [Assign.join_dom_eq, hdom', Assign.single_dom, hdom, Finset.insert_eq, Finset.union_comm]
      · intro p hp
        rw [Assign.mem_join_val, Assign.mem_restrict_val, mem_single, hdom']
        have hp1 : p.1 ∈ insert v (desc c) := by rw [← hdom]; exact Assign.fst_mem_dom hp
        rw [Finset.mem_insert] at hp1
        rcases hp1 with hp1 | hp1
        · right
          refine ⟨?_, by rw [hp1]; exact hv⟩
          have : p = pv := eq_of_mem_of_mem hp hpv (hp1.trans hpv1.symm)
          rw [this]
          exact Prod.ext hpv1 rfl
        · exact Or.inl ⟨hp, hp1⟩
  · rintro ⟨g', hg', d, hd, hcons, rfl⟩
    obtain ⟨hvals', hdom', hcons'⟩ := mem_cands.mp hg'
    have hv' : v ∉ g'.dom := by rw [hdom']; exact hv
    rw [consistent_iff] at hcons
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      rw [Assign.mem_join_val, mem_single] at hp
      rcases hp with hp | ⟨rfl, _⟩
      · exact ⟨Finset.mem_insert_of_mem (hvals' p hp).1, (hvals' p hp).2⟩
      · exact ⟨Finset.mem_insert_self _ _, hd⟩
    · rw [Assign.join_dom_eq, hdom', Assign.single_dom, Finset.union_comm, ← Finset.insert_eq]
    · intro p hp q hq he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨hp1, hq1⟩ := covered_sub_desc hc _ he
        have hp' := mem_join_single_of_ne hp (fun h => hv (h ▸ hp1))
        have hq' := mem_join_single_of_ne hq (fun h => hv (h ▸ hq1))
        exact hcons' p hp' q hq' he
      · rcases mem_newEdges.mp he with ⟨h1, h2, h3⟩ | ⟨h, hloop⟩
        · have hq' := mem_join_single_of_eq hq hv' h3
          have hp' := mem_join_single_of_ne hp (fun h => hv (h ▸ bag_sub_desc hc h1))
          rw [hq']
          exact hcons.1 p (Assign.mem_restrict_val.mpr ⟨hp', h1⟩) h2
        · have h' := Prod.mk.inj h
          have hp' := mem_join_single_of_eq hp hv' h'.1
          have hq' := mem_join_single_of_eq hq hv' h'.2
          rw [hp', hq']
          exact hcons.2 hloop

theorem cands_forget {P : Graphs} {v : Var} {c : Node HOp} :
    cands P (.mk (.forget v) [c]) = cands P c := by
  unfold cands
  rw [desc_forget, covered_forget]

/-- Candidates at `Join`: the unions of one candidate per side that agree on the bag. -/
theorem cands_join {P : Graphs} {a b : Node HOp} (ha : WF a) (hb : WF b) (hbag : bag a = bag b)
    (hmeet : desc a ∩ desc b ⊆ bag a) {g : Assign} :
    g ∈ cands P (.mk .join [a, b]) ↔
      ∃ g1 ∈ cands P a, ∃ g2 ∈ cands P b,
        g1.restrict (bag a) = g2.restrict (bag b) ∧ g = g1.join g2 := by
  rw [mem_cands, desc_join, covered_join]
  constructor
  · rintro ⟨hvals, hdom, hcons⟩
    have hdom1 : (g.restrict (desc a)).dom = desc a := by
      rw [Assign.restrict_dom, hdom]
      exact Finset.inter_eq_right.mpr Finset.subset_union_left
    have hdom2 : (g.restrict (desc b)).dom = desc b := by
      rw [Assign.restrict_dom, hdom]
      exact Finset.inter_eq_right.mpr Finset.subset_union_right
    refine ⟨g.restrict (desc a), ?_, g.restrict (desc b), ?_, ?_, ?_⟩
    · rw [mem_cands]
      refine ⟨?_, hdom1, consistentOn_restrict (consistentOn_mono Finset.subset_union_left hcons) _⟩
      intro p hp
      rw [Assign.mem_restrict_val] at hp
      exact ⟨hp.2, (hvals p hp.1).2⟩
    · rw [mem_cands]
      refine ⟨?_, hdom2, consistentOn_restrict (consistentOn_mono Finset.subset_union_right hcons) _⟩
      intro p hp
      rw [Assign.mem_restrict_val] at hp
      exact ⟨hp.2, (hvals p hp.1).2⟩
    · have hsub : bag a ⊆ desc b := by rw [hbag]; exact bag_sub_desc hb
      rw [restrict_restrict, restrict_restrict, Finset.inter_eq_right.mpr (bag_sub_desc ha),
        ← hbag, Finset.inter_eq_right.mpr hsub]
    · apply Assign.ext_of_dom_eq
      · rw [Assign.join_dom_eq, hdom1, hdom2, hdom]
      · intro p hp
        rw [Assign.mem_join_val, Assign.mem_restrict_val, Assign.mem_restrict_val, hdom1]
        have hp1 : p.1 ∈ desc a ∪ desc b := by rw [← hdom]; exact Assign.fst_mem_dom hp
        by_cases hpa : p.1 ∈ desc a
        · exact Or.inl ⟨hp, hpa⟩
        · rcases Finset.mem_union.mp hp1 with hp1 | hp1
          · exact absurd hp1 hpa
          · exact Or.inr ⟨⟨hp, hp1⟩, hpa⟩
  · rintro ⟨g1, hg1, g2, hg2, hres, rfl⟩
    obtain ⟨hvals1, hdom1, hcons1⟩ := mem_cands.mp hg1
    obtain ⟨hvals2, hdom2, hcons2⟩ := mem_cands.mp hg2
    have hcompat : Assign.Compat g1 g2 := by
      refine compat_of_restrict_eq (B := bag a) ?_ (by rw [hres, hbag])
      rw [hdom1, hdom2]
      exact hmeet
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      rw [Assign.join_val_of_compat hcompat, Finset.mem_union] at hp
      rcases hp with hp | hp
      · exact ⟨Finset.mem_union_left _ (hvals1 p hp).1, (hvals1 p hp).2⟩
      · exact ⟨Finset.mem_union_right _ (hvals2 p hp).1, (hvals2 p hp).2⟩
    · rw [Assign.join_dom_eq, hdom1, hdom2]
    · intro p hp q hq he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨hp1, hq1⟩ := covered_sub_desc ha _ he
        exact hcons1 p (mem_join_left_of_mem_dom hcompat hp (hdom1 ▸ hp1))
          q (mem_join_left_of_mem_dom hcompat hq (hdom1 ▸ hq1)) he
      · obtain ⟨hp1, hq1⟩ := covered_sub_desc hb _ he
        exact hcons2 p (mem_join_right_of_mem_dom hcompat hp (hdom2 ▸ hp1))
          q (mem_join_right_of_mem_dom hcompat hq (hdom2 ▸ hq1)) he

/-! ## The candidates built the generic way -/

/-- What `cand_iff` builds at `Introduce v` is the child's candidate extended by `v`. -/
theorem build_intro {g' : Assign} {v : Var} {d : Val} {o : Bool} (hv : v ∉ g'.dom) (B : Finset Var) :
    ((Assign.joinAll [g']).join (Assign.ofList (if o then [(v, d)] else []))).join
        ((Assign.single v d).join (g'.restrict B)) =
      g'.join (Assign.single v d) := by
  rw [joinAll_single]
  have hL : ∀ p ∈ (Assign.ofList (if o then [(v, d)] else [])).1, p = (v, d) := by
    intro p hp
    cases o with
    | true =>
      rw [if_pos rfl, ofList_single, mem_single] at hp
      exact hp
    | false =>
      rw [if_neg Bool.false_ne_true] at hp
      exact absurd hp (Finset.notMem_empty _)
  have hLdom : (Assign.ofList (if o then [(v, d)] else [])).dom ⊆ {v} := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := exists_mem_of_mem_dom hx
    rw [hL p hp]
    exact Finset.mem_singleton_self _
  apply Assign.ext_of_dom_eq
  · rw [Assign.join_dom_eq, Assign.join_dom_eq, Assign.join_dom_eq, Assign.single_dom,
      Assign.restrict_dom, Assign.join_dom_eq, Assign.single_dom]
    ext x
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_inter, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · rintro ((hx | hx) | (hx | ⟨hx, _⟩))
      · exact Or.inl hx
      · exact Or.inr (Finset.mem_singleton.mp (hLdom hx))
      · exact Or.inr hx
      · exact Or.inl hx
    · rintro (hx | hx)
      · exact Or.inl (Or.inl hx)
      · exact Or.inr (Or.inl hx)
  · intro p hp
    rw [Assign.mem_join_val, Assign.mem_join_val, Assign.mem_join_val, Assign.mem_restrict_val,
      mem_single] at hp
    rw [Assign.mem_join_val, mem_single]
    rcases hp with (hp | ⟨hp, _⟩) | ⟨hp | ⟨⟨hp, _⟩, _⟩, hpd⟩
    · exact Or.inl hp
    · rw [hL p hp]
      exact Or.inr ⟨rfl, hv⟩
    · subst hp
      exact Or.inr ⟨rfl, hv⟩
    · exfalso
      apply hpd
      rw [Assign.join_dom_eq]
      exact Finset.mem_union_left _ (Assign.fst_mem_dom hp)

theorem build_forget (g' : Assign) (B : Finset Var) (v : Var) :
    ((Assign.joinAll [g']).join (Assign.ofList [])).join
        ((g'.restrict B).restrict ((g'.restrict B).dom.erase v)) = g' := by
  rw [joinAll_single]
  show (g'.join Assign.empty).join _ = g'
  rw [Assign.join_empty]
  apply join_of_dom_sub
  rw [Assign.restrict_dom, Assign.restrict_dom]
  intro x hx
  exact (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1

theorem build_join (g1 g2 : Assign) (B : Finset Var) :
    ((Assign.joinAll [g1, g2]).join (Assign.ofList [])).join (g1.restrict B) = g1.join g2 := by
  rw [joinAll_pair]
  show ((g1.join g2).join Assign.empty).join _ = g1.join g2
  rw [Assign.join_empty]
  apply join_of_dom_sub
  rw [Assign.restrict_dom, Assign.join_dom_eq]
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).1

theorem build_leaf : ((Assign.joinAll []).join (Assign.ofList [])).join Assign.empty = Assign.empty := by
  show (Assign.empty.join Assign.empty).join Assign.empty = Assign.empty
  rw [Assign.join_empty, Assign.join_empty]

/-- The trace function. -/
abbrev trace (n : Node HOp) (g : Assign) : Assign := g.restrict (bag n)

theorem forall₂_single {R : Assign → Node HOp → Prop} {gs : List Assign} {c : Node HOp}
    (h : List.Forall₂ R gs [c]) : ∃ g, gs = [g] ∧ R g c := by
  obtain ⟨g, gs', hg, hnil, rfl⟩ := List.forall₂_cons_right_iff.mp h
  rw [List.forall₂_nil_right_iff.mp hnil]
  exact ⟨g, rfl, hg⟩

theorem forall₂_pair {R : Assign → Node HOp → Prop} {gs : List Assign} {a b : Node HOp}
    (h : List.Forall₂ R gs [a, b]) : ∃ g1 g2, gs = [g1, g2] ∧ R g1 a ∧ R g2 b := by
  obtain ⟨g1, gs', hg1, h', rfl⟩ := List.forall₂_cons_right_iff.mp h
  obtain ⟨g2, rfl, hg2⟩ := forall₂_single h'
  exact ⟨g1, g2, rfl, hg1, hg2⟩

/-- `cand_iff` for the instance. -/
theorem cand_iff (P : Graphs) (op : HOp) (cs : List (Node HOp)) (hwf : WF (.mk op cs)) (g : Assign) :
    g ∈ cands P (.mk op cs) ↔
      ∃ gs : List Assign, List.Forall₂ (fun g' c => g' ∈ cands P c) gs cs ∧
        gs.Pairwise Assign.Compat ∧
        ∃ out ∈ step P op (List.zipWith trace cs gs),
          g = ((Assign.joinAll gs).join (Assign.ofList out.2)).join out.1 := by
  cases hwf with
  | leaf =>
    rw [cands_leaf]
    constructor
    · rintro rfl
      refine ⟨[], List.Forall₂.nil, List.Pairwise.nil, (Assign.empty, []),
        List.mem_singleton.mpr rfl, ?_⟩
      exact build_leaf.symm
    · rintro ⟨gs, hgs, _, out, hout, rfl⟩
      rw [List.forall₂_nil_right_iff.mp hgs] at hout ⊢
      have hout' : out ∈ [(Assign.empty, ([] : List (Var × Val)))] := hout
      rw [List.mem_singleton] at hout'
      subst hout'
      exact build_leaf
  | @intro v o c hc hv =>
    rw [cands_intro hc hv]
    constructor
    · rintro ⟨g', hg', d, hd, hcons, rfl⟩
      have hv' : v ∉ g'.dom := by rw [(mem_cands.mp hg').2.1]; exact hv
      refine ⟨[g'], List.forall₂_cons.mpr ⟨hg', List.Forall₂.nil⟩, List.pairwise_singleton _ _,
        ((Assign.single v d).join (g'.restrict (bag c)), if o then [(v, d)] else []),
        step_intro_mem.mpr ⟨d, hd, hcons, rfl⟩, ?_⟩
      exact (build_intro hv' (bag c)).symm
    · rintro ⟨gs, hgs, _, out, hout, rfl⟩
      obtain ⟨g', rfl, hg'⟩ := forall₂_single hgs
      have hv' : v ∉ g'.dom := by rw [(mem_cands.mp hg').2.1]; exact hv
      obtain ⟨d, hd, hcons, rfl⟩ := step_intro_mem.mp hout
      refine ⟨g', hg', d, hd, hcons, ?_⟩
      exact build_intro hv' (bag c)
  | @forget v c hc hvb hvo =>
    rw [cands_forget]
    constructor
    · intro hg
      refine ⟨[g], List.forall₂_cons.mpr ⟨hg, List.Forall₂.nil⟩, List.pairwise_singleton _ _,
        ((g.restrict (bag c)).restrict ((g.restrict (bag c)).dom.erase v), []),
        List.mem_singleton.mpr rfl, ?_⟩
      exact (build_forget g (bag c) v).symm
    · rintro ⟨gs, hgs, _, out, hout, rfl⟩
      obtain ⟨g', rfl, hg'⟩ := forall₂_single hgs
      have hout' : out ∈ [((g'.restrict (bag c)).restrict ((g'.restrict (bag c)).dom.erase v),
        ([] : List (Var × Val)))] := hout
      rw [List.mem_singleton] at hout'
      subst hout'
      show ((Assign.joinAll [g']).join (Assign.ofList [])).join
        ((g'.restrict (bag c)).restrict ((g'.restrict (bag c)).dom.erase v)) ∈ cands P c
      rw [build_forget]
      exact hg'
  | @join a b ha hb hbag hmeet _ =>
    rw [cands_join ha hb hbag hmeet]
    constructor
    · rintro ⟨g1, hg1, g2, hg2, hres, rfl⟩
      have hcompat : Assign.Compat g1 g2 := by
        refine compat_of_restrict_eq (B := bag a) ?_ (by rw [hres, hbag])
        rw [(mem_cands.mp hg1).2.1, (mem_cands.mp hg2).2.1]
        exact hmeet
      refine ⟨[g1, g2], List.forall₂_cons.mpr ⟨hg1, List.forall₂_cons.mpr ⟨hg2, List.Forall₂.nil⟩⟩,
        ?_, (g1.restrict (bag a), []), step_join_mem.mpr ⟨hres, rfl⟩, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, List.pairwise_singleton _ _⟩
        intro g' hg'
        rw [List.mem_singleton] at hg'
        subst hg'
        exact hcompat
      · exact (build_join g1 g2 (bag a)).symm
    · rintro ⟨gs, hgs, _, out, hout, rfl⟩
      obtain ⟨g1, g2, rfl, hg1, hg2⟩ := forall₂_pair hgs
      obtain ⟨hres, rfl⟩ := step_join_mem.mp hout
      exact ⟨g1, hg1, g2, hg2, hres, build_join g1 g2 (bag a)⟩

theorem step_compat (P : Graphs) (op : HOp) (cs : List (Node HOp)) (gs : List Assign)
    (hwf : WF (.mk op cs)) (hgs : List.Forall₂ (fun g c => g ∈ cands P c) gs cs) :
    ∀ out ∈ step P op (List.zipWith trace cs gs), gs.Pairwise Assign.Compat := by
  intro out hout
  cases hwf with
  | leaf =>
    rw [List.forall₂_nil_right_iff.mp hgs]
    exact List.Pairwise.nil
  | intro _ _ =>
    obtain ⟨g', rfl, _⟩ := forall₂_single hgs
    exact List.pairwise_singleton _ _
  | forget _ _ _ =>
    obtain ⟨g', rfl, _⟩ := forall₂_single hgs
    exact List.pairwise_singleton _ _
  | @join a b _ _ hbag hmeet _ =>
    obtain ⟨g1, g2, rfl, hg1, hg2⟩ := forall₂_pair hgs
    obtain ⟨hres, _⟩ := step_join_mem.mp hout
    have hcompat : Assign.Compat g1 g2 := by
      refine compat_of_restrict_eq (B := bag a) ?_ (by rw [hres, hbag])
      rw [(mem_cands.mp hg1).2.1, (mem_cands.mp hg2).2.1]
      exact hmeet
    rw [List.pairwise_cons]
    refine ⟨?_, List.pairwise_singleton _ _⟩
    intro g' hg'
    rw [List.mem_singleton] at hg'
    subst hg'
    exact hcompat

theorem trace_mk (P : Graphs) (op : HOp) (cs : List (Node HOp)) (gs : List Assign)
    (out : Assign × List (Var × Val)) (hwf : WF (.mk op cs))
    (hgs : List.Forall₂ (fun g c => g ∈ cands P c) gs cs)
    (hout : out ∈ step P op (List.zipWith trace cs gs)) :
    trace (.mk op cs) (((Assign.joinAll gs).join (Assign.ofList out.2)).join out.1) = out.1 := by
  cases hwf with
  | leaf =>
    rw [List.forall₂_nil_right_iff.mp hgs] at hout ⊢
    have hout' : out ∈ [(Assign.empty, ([] : List (Var × Val)))] := hout
    rw [List.mem_singleton] at hout'
    subst hout'
    show (((Assign.joinAll []).join (Assign.ofList [])).join Assign.empty).restrict (bag _) =
      Assign.empty
    rw [build_leaf, bag_leaf, restrict_empty_set]
  | @intro v o c hc hv =>
    obtain ⟨g', rfl, hg'⟩ := forall₂_single hgs
    have hv' : v ∉ g'.dom := by rw [(mem_cands.mp hg').2.1]; exact hv
    obtain ⟨d, _, _, rfl⟩ := step_intro_mem.mp hout
    show ((((Assign.joinAll [g']).join (Assign.ofList (if o then [(v, d)] else []))).join
      ((Assign.single v d).join (g'.restrict (bag c)))).restrict (bag (.mk (.intro v o) [c]))) =
      (Assign.single v d).join (g'.restrict (bag c))
    rw [build_intro hv' (bag c), bag_intro, restrict_join_single hv']
  | @forget v c hc hvb _ =>
    obtain ⟨g', rfl, hg'⟩ := forall₂_single hgs
    have hout' : out ∈ [((g'.restrict (bag c)).restrict ((g'.restrict (bag c)).dom.erase v),
      ([] : List (Var × Val)))] := hout
    rw [List.mem_singleton] at hout'
    subst hout'
    show (((Assign.joinAll [g']).join (Assign.ofList [])).join
      ((g'.restrict (bag c)).restrict ((g'.restrict (bag c)).dom.erase v))).restrict
        (bag (.mk (.forget v) [c])) =
      (g'.restrict (bag c)).restrict ((g'.restrict (bag c)).dom.erase v)
    have hdom : (g'.restrict (bag c)).dom = bag c := by
      rw [Assign.restrict_dom, (mem_cands.mp hg').2.1]
      exact Finset.inter_eq_right.mpr (bag_sub_desc hc)
    rw [build_forget, bag_forget, hdom, restrict_restrict,
      Finset.inter_eq_right.mpr (Finset.erase_subset _ _)]
  | @join a b ha _ _ _ _ =>
    obtain ⟨g1, g2, rfl, hg1, _⟩ := forall₂_pair hgs
    obtain ⟨_, rfl⟩ := step_join_mem.mp hout
    show (((Assign.joinAll [g1, g2]).join (Assign.ofList [])).join (g1.restrict (bag a))).restrict
      (bag (.mk .join [a, b])) = g1.restrict (bag a)
    rw [build_join, bag_join]
    apply Assign.restrict_join_left_of_subset
    rw [(mem_cands.mp hg1).2.1]
    exact bag_sub_desc ha

theorem opOwned_disjoint (op : HOp) (cs : List (Node HOp)) (hwf : WF (.mk op cs)) :
    ∀ c ∈ cs, Disjoint (opOwned op) (desc c) := by
  intro c hc
  cases hwf with
  | leaf => nomatch hc
  | @intro v o c' _ hv =>
    rw [List.mem_singleton] at hc
    subst hc
    show Disjoint (if o then {v} else ∅) (desc c)
    split
    · rw [Finset.disjoint_singleton_left]
      exact hv
    · exact Finset.disjoint_empty_left _
  | forget _ _ _ => exact Finset.disjoint_empty_left _
  | join _ _ _ _ _ => exact Finset.disjoint_empty_left _

theorem children_owned_disjoint (op : HOp) (cs : List (Node HOp)) (hwf : WF (.mk op cs)) :
    (cs.map owned).Pairwise Disjoint := by
  cases hwf with
  | leaf => exact List.Pairwise.nil
  | intro _ _ => exact List.pairwise_singleton _ _
  | forget _ _ _ => exact List.pairwise_singleton _ _
  | @join a b _ _ _ _ hown =>
    show [owned a, owned b].Pairwise Disjoint
    rw [List.pairwise_cons]
    refine ⟨?_, List.pairwise_singleton _ _⟩
    intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    exact hown

theorem determined (P : Graphs) (n : Node HOp) (hwf : WF n) :
    ∀ g ∈ cands P n, ∀ g' ∈ cands P n,
      g.restrict (owned n) = g'.restrict (owned n) → trace n g = trace n g' → g = g' := by
  intro g hg g' hg' hown htr
  apply Assign.ext_of_dom_eq
  · rw [(mem_cands.mp hg).2.1, (mem_cands.mp hg').2.1]
  · intro p hp
    have hp1 : p.1 ∈ owned n ∪ bag n := by
      apply desc_sub_owned_union_bag hwf
      rw [← (mem_cands.mp hg).2.1]
      exact Assign.fst_mem_dom hp
    rcases Finset.mem_union.mp hp1 with hp1 | hp1
    · have h : p ∈ (g.restrict (owned n)).1 := Assign.mem_restrict_val.mpr ⟨hp, hp1⟩
      rw [hown, Assign.mem_restrict_val] at h
      exact h.1
    · have h : p ∈ (g.restrict (bag n)).1 := Assign.mem_restrict_val.mpr ⟨hp, hp1⟩
      have h2 : (g.restrict (bag n)).1 = (g'.restrict (bag n)).1 := congrArg Subtype.val htr
      rw [h2, Assign.mem_restrict_val] at h
      exact h.1

/-- The instance. -/
def inst (P : Graphs) : OwnedInstance HOp Assign where
  step := step P
  accept := fun τ => decide (τ = Assign.empty)
  cands := cands P
  trace := trace
  WF := WF
  wf_children := wf_children
  dom := desc
  dom_eq := fun _ _ g hg => (mem_cands.mp hg).2.1
  owned := owned
  opOwned := opOwned
  owned_mk := fun op cs _ => owned_mk op cs
  owned_sub := fun _ h => owned_sub_desc h
  opOwned_disjoint := opOwned_disjoint
  children_owned_disjoint := children_owned_disjoint
  step_leaves := step_leaves P
  step_nodup := step_nodup P
  tauAssign := fun τ => τ
  cand_iff := cand_iff P
  step_compat := step_compat P
  trace_mk := trace_mk P
  determined := determined P
  accept_determined := fun _ _ g _ g' _ h1 h2 _ =>
    (decide_eq_true_iff.mp h1).trans (decide_eq_true_iff.mp h2).symm
  solution := fun n g => trace n g = Assign.empty
  accept_iff := fun _ _ _ => decide_eq_true_iff.symm

/-! ## Claim 1 for H-colouring -/

/-- At a root with an empty bag every candidate is accepted and is its own owned part. -/
theorem restrict_owned_eq {P : Graphs} {n : Node HOp} (hwf : WF n) (hroot : bag n = ∅)
    {g : Assign} (hg : g ∈ cands P n) : g.restrict (owned n) = g := by
  apply restrict_of_dom_sub
  rw [(mem_cands.mp hg).2.1]
  have h := desc_sub_owned_union_bag hwf
  rw [hroot, Finset.union_empty] at h
  exact h

/-- Claim 1: the DP's expression at a root with an empty bag denotes exactly the candidates,
    the colourings of the subtree's vertices that respect every checked edge. -/
theorem solve_sound (P : Graphs) {n : Node HOp} (hwf : WF n) (hroot : bag n = ∅) :
    Sem ((inst P).toTraced.solve n) (cands P n) := by
  have h := (inst P).solve_sound hwf
  have hset : (((inst P).cands n).filter fun g => (inst P).accept ((inst P).trace n g) = true).image
      (fun g => g.restrict ((inst P).owned n)) = cands P n := by
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
      show decide (x.restrict (bag n) = Assign.empty) = true
      rw [decide_eq_true_iff, hroot]
      exact restrict_empty_set x
  rw [hset] at h
  exact h

/-- The `H`-colourings of `G` on the vertices `V`: total on `V`, colours below `nH`, every edge
    of `G` within `V` sent to an edge of `H`. -/
def Hom (P : Graphs) (V : Finset Var) : Finset Assign :=
  (allAssign V P.nH).filter fun g =>
    g.dom = V ∧ ∀ p ∈ g.1, ∀ q ∈ g.1, P.adjG p.1 q.1 = true → P.adjH p.2 q.2 = true

/-- When the checked edges are all of `G`'s edges among the subtree's vertices (Lemma 2, which
    the Rust validates) and `H` is undirected, the candidates are the `H`-colourings. -/
theorem cands_eq_hom {P : Graphs} {n : Node HOp} (hwf : WF n)
    (hcov : ∀ u ∈ desc n, ∀ w ∈ desc n, P.adjG u w = true →
      (u, w) ∈ covered P n ∨ (w, u) ∈ covered P n)
    (hsymm : ∀ c d, P.adjH c d = P.adjH d c) : cands P n = Hom P (desc n) := by
  ext g
  rw [mem_cands, Hom, Finset.mem_filter, mem_allAssign]
  constructor
  · rintro ⟨hvals, hdom, hcons⟩
    refine ⟨hvals, hdom, ?_⟩
    intro p hp q hq hadj
    have hp1 : p.1 ∈ desc n := by rw [← hdom]; exact Assign.fst_mem_dom hp
    have hq1 : q.1 ∈ desc n := by rw [← hdom]; exact Assign.fst_mem_dom hq
    rcases hcov p.1 hp1 q.1 hq1 hadj with he | he
    · exact hcons p hp q hq he
    · rw [hsymm]
      exact hcons q hq p hp he
  · rintro ⟨hvals, hdom, hhom⟩
    refine ⟨hvals, hdom, ?_⟩
    intro p hp q hq he
    exact hhom p hp q hq (covered_adj hwf _ he)

/-- Claim 1 for H-colouring: on a nice tree decomposition whose root bag is empty and which
    checks every edge of `G`, the DP's expression denotes exactly the `H`-colourings of `G`. -/
theorem hcol_sound (P : Graphs) {n : Node HOp} (hwf : WF n) (hroot : bag n = ∅)
    (hcov : ∀ u ∈ desc n, ∀ w ∈ desc n, P.adjG u w = true →
      (u, w) ∈ covered P n ∨ (w, u) ∈ covered P n)
    (hsymm : ∀ c d, P.adjH c d = P.adjH d c) :
    Sem ((inst P).toTraced.solve n) (Hom P (desc n)) := by
  rw [← cands_eq_hom hwf hcov hsymm]
  exact solve_sound P hwf hroot

end Formalism.HCol
