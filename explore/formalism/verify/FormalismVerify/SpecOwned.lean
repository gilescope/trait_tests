import FormalismVerify.Spec

/-!
# Claim 1 when siblings share variables

`Instance` (in `Spec.lean`) has every candidate assign exactly the variables its subtree owns,
and a trace that is a function of that assignment. Tree-decomposition instances do not fit: a
vertex that is in both children's bags of a `Join` is a candidate variable of both subtrees but
owned by one, and a non-owner `Introduce` records the vertex's colour in the trace while the
owned part of the candidate does not mention it. So here a candidate is a full partial solution
on the subtree's variables (`dom`), a row denotes the *owned parts* of the candidates with its
trace, the children's candidates are combined by a compatible union rather than a disjoint
join, and two obligations replace "trace is a function of the owned part": a candidate is
determined by its owned part and its trace (`determined`), and among accepted traces the owned
part alone determines the trace (`accept_determined`). `Instance` is the special case where
everything is owned.
-/

namespace Formalism

/-! ## Compatible assignments -/

namespace Assign

/-- Two assignments agree wherever both are defined. -/
def Compat (f g : Assign) : Prop := ∀ p ∈ f.1, ∀ q ∈ g.1, p.1 = q.1 → p = q

theorem Compat.symm {f g : Assign} (h : Compat f g) : Compat g f :=
  fun q hq p hp hqp => (h p hp q hq hqp.symm).symm

theorem compat_of_disjoint {f g : Assign} (h : Disjoint f.dom g.dom) : Compat f g := by
  intro p hp q hq hpq
  exfalso
  have h1 : p.1 ∉ g.dom := Finset.disjoint_left.mp h (fst_mem_dom hp)
  rw [hpq] at h1
  exact h1 (fst_mem_dom hq)

theorem compat_empty (g : Assign) : Compat empty g :=
  fun p hp => absurd hp (Finset.notMem_empty p)

theorem compat_self (g : Assign) : Compat g g := g.2

theorem compat_of_pairwise : ∀ {gs : List Assign}, gs.Pairwise Compat →
    ∀ g ∈ gs, ∀ g' ∈ gs, Compat g g'
  | [], _, _, hg, _, _ => nomatch hg
  | a :: gs, hp, g, hg, g', hg' => by
    rw [List.pairwise_cons] at hp
    rw [List.mem_cons] at hg hg'
    rcases hg with rfl | hg <;> rcases hg' with rfl | hg'
    · exact compat_self _
    · exact hp.1 _ hg'
    · exact (hp.1 _ hg).symm
    · exact compat_of_pairwise hp.2 g hg g' hg'

theorem mem_join_val {f g : Assign} {q : Var × Val} :
    q ∈ (f.join g).1 ↔ q ∈ f.1 ∨ (q ∈ g.1 ∧ q.1 ∉ f.dom) := by
  show q ∈ f.1 ∪ g.1.filter (fun q => q.1 ∉ f.dom) ↔ _
  rw [Finset.mem_union, Finset.mem_filter]

theorem join_val_of_compat {f g : Assign} (h : Compat f g) : (f.join g).1 = f.1 ∪ g.1 := by
  ext q
  rw [mem_join_val, Finset.mem_union]
  constructor
  · rintro (hq | ⟨hq, _⟩)
    · exact Or.inl hq
    · exact Or.inr hq
  · rintro (hq | hq)
    · exact Or.inl hq
    · by_cases hd : q.1 ∈ f.dom
      · rw [dom, Finset.mem_image] at hd
        obtain ⟨p, hp, hpq⟩ := hd
        rw [← h p hp q hq hpq]
        exact Or.inl hp
      · exact Or.inr ⟨hq, hd⟩

theorem Compat.join_left {e g g' : Assign} (h1 : Compat e g') (h2 : Compat g g') :
    Compat (e.join g) g' := by
  intro p hp q hq hpq
  rw [mem_join_val] at hp
  rcases hp with hp | ⟨hp, _⟩
  · exact h1 p hp q hq hpq
  · exact h2 p hp q hq hpq

theorem join_dom_eq (f g : Assign) : (f.join g).dom = f.dom ∪ g.dom := by
  apply Finset.Subset.antisymm (join_dom_subset f g)
  intro x hx
  rw [Finset.mem_union] at hx
  rw [dom, Finset.mem_image]
  rcases hx with hx | hx
  · rw [dom, Finset.mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, mem_join_val.mpr (Or.inl hp), rfl⟩
  · by_cases hf : x ∈ f.dom
    · rw [dom, Finset.mem_image] at hf
      obtain ⟨p, hp, rfl⟩ := hf
      exact ⟨p, mem_join_val.mpr (Or.inl hp), rfl⟩
    · rw [dom, Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      exact ⟨p, mem_join_val.mpr (Or.inr ⟨hp, hf⟩), rfl⟩

theorem mem_restrict_val {f : Assign} {D : Finset Var} {p : Var × Val} :
    p ∈ (f.restrict D).1 ↔ p ∈ f.1 ∧ p.1 ∈ D := by
  show p ∈ f.1.filter (fun p => p.1 ∈ D) ↔ _
  rw [Finset.mem_filter]

theorem restrict_dom (f : Assign) (D : Finset Var) : (f.restrict D).dom = f.dom ∩ D := by
  ext x
  rw [dom, Finset.mem_image, Finset.mem_inter, dom, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_restrict_val] at hp
    exact ⟨⟨p, hp.1, rfl⟩, hp.2⟩
  · rintro ⟨⟨p, hp, rfl⟩, hD⟩
    exact ⟨p, mem_restrict_val.mpr ⟨hp, hD⟩, rfl⟩

/-- Assignments with the same domain, one included in the other, are equal. -/
theorem ext_of_dom_eq {f g : Assign} (hd : f.dom = g.dom) (hsub : ∀ p ∈ f.1, p ∈ g.1) : f = g := by
  apply Subtype.ext
  apply Finset.Subset.antisymm hsub
  intro q hq
  have hqd : q.1 ∈ f.dom := by rw [hd]; exact fst_mem_dom hq
  rw [dom, Finset.mem_image] at hqd
  obtain ⟨p, hp, hpq⟩ := hqd
  rw [← g.2 p (hsub p hp) q hq hpq]
  exact hp

/-- Restricting to variables `f` has ignores `g` (the join is left-biased). -/
theorem restrict_join_left_of_subset {f g : Assign} {D : Finset Var} (h : D ⊆ f.dom) :
    (f.join g).restrict D = f.restrict D := by
  apply Subtype.ext
  ext p
  rw [mem_restrict_val, mem_restrict_val, mem_join_val]
  constructor
  · rintro ⟨hp | ⟨_, hpd⟩, hD⟩
    · exact ⟨hp, hD⟩
    · exact absurd (h hD) hpd
  · rintro ⟨hp, hD⟩
    exact ⟨Or.inl hp, hD⟩

/-- With compatible arguments the join restricts to the right argument on its domain. -/
theorem restrict_join_right_of_compat {f g : Assign} (h : Compat f g) :
    (f.join g).restrict g.dom = g := by
  apply Subtype.ext
  ext p
  rw [mem_restrict_val, join_val_of_compat h, Finset.mem_union]
  constructor
  · rintro ⟨hp | hp, hD⟩
    · rw [dom, Finset.mem_image] at hD
      obtain ⟨q, hq, hqp⟩ := hD
      rw [h p hp q hq hqp.symm]
      exact hq
    · exact hp
  · intro hp
    exact ⟨Or.inr hp, fst_mem_dom hp⟩

theorem restrict_foldl_join_of_subset {D : Finset Var} :
    ∀ (fs : List Assign) (e : Assign), D ⊆ e.dom → (fs.foldl join e).restrict D = e.restrict D
  | [], _, _ => rfl
  | g :: fs, e, h => by
    rw [List.foldl_cons, restrict_foldl_join_of_subset fs (e.join g)
      (by rw [join_dom_eq]; exact h.trans Finset.subset_union_left)]
    exact restrict_join_left_of_subset h

/-- The join of pairwise compatible assignments restricts to each of them on its domain. -/
theorem restrict_foldl_join_mem :
    ∀ (fs : List Assign) (e : Assign), (∀ g ∈ fs, Compat e g) → fs.Pairwise Compat →
      ∀ g ∈ fs, (fs.foldl join e).restrict g.dom = g
  | [], _, _, _, _, hg => nomatch hg
  | g' :: fs, e, he, hp, g, hg => by
    rw [List.pairwise_cons] at hp
    rw [List.mem_cons] at hg
    rw [List.foldl_cons]
    rcases hg with rfl | hg
    · rw [restrict_foldl_join_of_subset fs (e.join g)
        (by rw [join_dom_eq]; exact Finset.subset_union_right)]
      exact restrict_join_right_of_compat (he g (List.mem_cons_self ..))
    · exact restrict_foldl_join_mem fs (e.join g')
        (fun g'' hg'' => Compat.join_left (he g'' (List.mem_cons_of_mem _ hg'')) (hp.1 g'' hg''))
        hp.2 g hg

/-- The pairs of a join of pairwise compatible assignments. -/
theorem foldl_join_val_of_compat :
    ∀ (fs : List Assign) (e : Assign), (∀ g ∈ fs, Compat e g) → fs.Pairwise Compat →
      (fs.foldl join e).1 = e.1 ∪ (fs.map Subtype.val).foldr (· ∪ ·) ∅
  | [], e, _, _ => by simp
  | g :: fs, e, he, hp => by
    rw [List.pairwise_cons] at hp
    rw [List.foldl_cons, List.map_cons, List.foldr_cons,
      foldl_join_val_of_compat fs (e.join g)
        (fun g' hg' => Compat.join_left (he g' (List.mem_cons_of_mem _ hg')) (hp.1 g' hg')) hp.2,
      join_val_of_compat (he g (List.mem_cons_self ..)), Finset.union_assoc]

theorem dom_foldl_join_eq :
    ∀ (fs : List Assign) (e : Assign),
      (fs.foldl join e).dom = e.dom ∪ (fs.map dom).foldr (· ∪ ·) ∅
  | [], e => by simp
  | g :: fs, e => by
    rw [List.foldl_cons, List.map_cons, List.foldr_cons, dom_foldl_join_eq fs, join_dom_eq,
      Finset.union_assoc]

theorem joinAll_val_of_compat {gs : List Assign} (h : gs.Pairwise Compat) :
    (joinAll gs).1 = (gs.map Subtype.val).foldr (· ∪ ·) ∅ := by
  unfold joinAll
  rw [foldl_join_val_of_compat gs empty (fun g _ => compat_empty g) h]
  show (∅ : Finset (Var × Val)) ∪ _ = _
  rw [Finset.empty_union]

theorem joinAll_dom (gs : List Assign) : (joinAll gs).dom = (gs.map dom).foldr (· ∪ ·) ∅ := by
  unfold joinAll
  rw [dom_foldl_join_eq, empty_dom, Finset.empty_union]

theorem restrict_joinAll_mem {gs : List Assign} (h : gs.Pairwise Compat) {g : Assign} (hg : g ∈ gs) :
    (joinAll gs).restrict g.dom = g :=
  restrict_foldl_join_mem gs empty (fun g _ => compat_empty g) h g hg

end Assign

theorem mem_foldr_union_of_mem {α : Type*} [DecidableEq α] :
    ∀ (l : List (Finset α)) {A : Finset α} {x : α}, A ∈ l → x ∈ A → x ∈ l.foldr (· ∪ ·) ∅
  | [], _, _, hA, _ => nomatch hA
  | B :: l, A, x, hA, hx => by
    rw [List.foldr_cons, Finset.mem_union]
    rw [List.mem_cons] at hA
    rcases hA with rfl | hA
    · exact Or.inl hx
    · exact Or.inr (mem_foldr_union_of_mem l hA hx)

/-! ## The Traced-level lemmas, with disjointness asked only where rows meet -/

namespace Traced
variable {Op Tau : Type*} [DecidableEq Tau]

/-- `TableSem.foldl_unionInto` with disjointness asked only of items that land in the same row. -/
theorem TableSem.foldl_unionInto' {Dn : Finset Var} (D : Tau × Expr → Finset Assign) :
    ∀ (items : List (Tau × Expr)) {T : Table Tau} {S : Tau → Finset Assign}, TableSem T S →
      (∀ it ∈ items, Sem it.2 (D it)) →
      items.Pairwise (fun a b => a.1 = b.1 → Disjoint (D a) (D b)) →
      (∀ it ∈ items, Disjoint (S it.1) (D it)) →
      (∀ it ∈ items, ∀ f ∈ D it, f.dom = Dn) →
      (∀ τ, ∀ f ∈ S τ, f.dom = Dn) →
      TableSem (items.foldl (fun T it => Traced.unionInto T it.1 it.2) T) fun τ =>
        S τ ∪ itemsSet D items τ
  | [], T, S, hT, _, _, _, _, _ => by
    intro τ
    simpa [itemsSet] using hT τ
  | it :: items, T, S, hT, hD, hpair, hS, hdomD, hdomS => by
    rw [List.pairwise_cons] at hpair
    have hT' := TableSem.unionInto_sem hT (hD it (List.mem_cons_self ..))
      (hS it (List.mem_cons_self ..))
      (fun f hf g hg => by rw [hdomS _ f hf, hdomD it (List.mem_cons_self ..) g hg])
    have ih := TableSem.foldl_unionInto' (Dn := Dn) D items hT'
      (fun it' h => hD it' (List.mem_cons_of_mem _ h)) hpair.2
      (fun it' h => by
        by_cases heq : it'.1 = it.1
        · simp only [heq, ite_true]
          exact Finset.disjoint_union_left.mpr
            ⟨heq ▸ hS it' (List.mem_cons_of_mem _ h), hpair.1 it' h heq.symm⟩
        · simp only [heq, ite_false]
          exact hS it' (List.mem_cons_of_mem _ h))
      (fun it' h => hdomD it' (List.mem_cons_of_mem _ h))
      (fun τ f hf => by
        by_cases heq : τ = it.1
        · simp only [heq, ite_true, Finset.mem_union] at hf
          rcases hf with hf | hf
          · exact hdomS _ f hf
          · exact hdomD it (List.mem_cons_self ..) f hf
        · simp only [heq, ite_false] at hf
          exact hdomS _ f hf)
    intro τ
    have := ih τ
    simp only [List.foldl_cons]
    by_cases heq : it.1 = τ
    · subst heq
      simpa [itemsSet, Finset.union_assoc] using this
    · simpa [itemsSet, heq, Ne.symm heq] using this

/-- `Sem.foldl_accept` with disjointness asked only of accepted rows. -/
theorem Sem.foldl_accept' {Dn : Finset Var} (I : Traced Op Tau) (S : Tau → Finset Assign)
    (hS : ∀ τ τ', τ ≠ τ' → I.accept τ = true → I.accept τ' = true → Disjoint (S τ) (S τ'))
    (hdom : ∀ τ, ∀ f ∈ S τ, f.dom = Dn) :
    ∀ (L : List (Tau × Expr)) (e : Expr) (A : Finset Assign), Sem e A →
      (L.map Prod.fst).Nodup → (∀ row ∈ L, Sem row.2 (S row.1)) →
      (∀ row ∈ L, I.accept row.1 = true → Disjoint A (S row.1)) → (∀ f ∈ A, f.dom = Dn) →
      Sem (L.foldl (fun e row => if I.accept row.1 then Expr.union' e row.2 else e) e)
        (A ∪ acceptedSet I S L)
  | [], e, A, he, _, _, _, _ => by simpa [acceptedSet] using he
  | row :: L, e, A, he, hnd, hL, hA, hAd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    by_cases h : I.accept row.1 = true
    · rw [ite_eq_left h]
      have hdisjL : ∀ r ∈ L, I.accept r.1 = true → Disjoint (S row.1) (S r.1) := by
        intro r hr hacc
        apply hS _ _ _ h hacc
        intro heq
        exact hnd.1 (heq ▸ List.mem_map.mpr ⟨r, hr, rfl⟩)
      have ih := Sem.foldl_accept' (Dn := Dn) I S hS hdom L (Expr.union' e row.2) (A ∪ S row.1)
        (Sem.union' he (hL row (List.mem_cons_self ..)) (hA row (List.mem_cons_self ..) h)
          (fun f hf g hg => by rw [hAd f hf, hdom _ g hg]))
        hnd.2 (fun r hr => hL r (List.mem_cons_of_mem _ hr))
        (fun r hr hacc => Finset.disjoint_union_left.mpr
          ⟨hA r (List.mem_cons_of_mem _ hr) hacc, hdisjL r hr hacc⟩)
        (fun f hf => by
          rw [Finset.mem_union] at hf
          rcases hf with hf | hf
          · exact hAd f hf
          · exact hdom _ f hf)
      rw [acceptedSet_cons, ite_eq_left h, ← Finset.union_assoc]
      exact ih
    · rw [ite_eq_right h]
      rw [acceptedSet_cons, ite_eq_right h]
      exact Sem.foldl_accept' (Dn := Dn) I S hS hdom L e A he hnd.2
        (fun r hr => hL r (List.mem_cons_of_mem _ hr))
        (fun r hr hacc => hA r (List.mem_cons_of_mem _ hr) hacc) hAd

end Traced

/-! ## Instances with shared variables -/

/-- An instance whose candidates are full partial solutions on the subtree's variables `dom`,
    of which the subtree owns `owned`; a row denotes the owned parts of the candidates with its
    trace. -/
structure OwnedInstance (Op Tau : Type*) extends Traced Op Tau where
  cands : Node Op → Finset Assign
  trace : Node Op → Assign → Tau
  WF : Node Op → Prop
  wf_children : ∀ (op : Op) (cs : List (Node Op)), WF (.mk op cs) → ∀ c ∈ cs, WF c
  /-- Variables every candidate of a node assigns. -/
  dom : Node Op → Finset Var
  dom_eq : ∀ n, WF n → ∀ g ∈ cands n, g.dom = dom n
  /-- Variables whose leaves live in the subtree: the operation's own and the children's. -/
  owned : Node Op → Finset Var
  opOwned : Op → Finset Var
  owned_mk : ∀ (op : Op) (cs : List (Node Op)), WF (.mk op cs) →
    owned (.mk op cs) = opOwned op ∪ (cs.map owned).foldr (· ∪ ·) ∅
  owned_sub : ∀ n, WF n → owned n ⊆ dom n
  opOwned_disjoint : ∀ (op : Op) (cs : List (Node Op)), WF (.mk op cs) →
    ∀ c ∈ cs, Disjoint (opOwned op) (dom c)
  children_owned_disjoint : ∀ (op : Op) (cs : List (Node Op)), WF (.mk op cs) →
    (cs.map owned).Pairwise Disjoint
  step_leaves : ∀ (op : Op) (taus : List Tau), ∀ out ∈ step op taus,
    (out.2.map Prod.fst).Nodup ∧ (out.2.map Prod.fst).toFinset = opOwned op
  step_nodup : ∀ (op : Op) (taus : List Tau),
    ((step op taus).map fun out => Assign.ofList out.2).Nodup
  /-- The candidates at a node are the compatible unions of one candidate per child with the
      leaves `step` yields for their traces. -/
  cand_iff : ∀ (op : Op) (cs : List (Node Op)), WF (.mk op cs) → ∀ g : Assign,
    g ∈ cands (.mk op cs) ↔
    ∃ gs : List Assign, List.Forall₂ (fun g' c => g' ∈ cands c) gs cs ∧
      gs.Pairwise Assign.Compat ∧
      ∃ out ∈ step op (List.zipWith trace cs gs),
        g = (Assign.joinAll gs).join (Assign.ofList out.2)
  /-- `step` only combines compatible candidates. -/
  step_compat : ∀ (op : Op) (cs : List (Node Op)) (gs : List Assign), WF (.mk op cs) →
    List.Forall₂ (fun g c => g ∈ cands c) gs cs →
    ∀ out ∈ step op (List.zipWith trace cs gs), gs.Pairwise Assign.Compat
  trace_mk : ∀ (op : Op) (cs : List (Node Op)) (gs : List Assign) (out : Tau × List (Var × Val)),
    WF (.mk op cs) → List.Forall₂ (fun g c => g ∈ cands c) gs cs →
    out ∈ step op (List.zipWith trace cs gs) →
    trace (.mk op cs) ((Assign.joinAll gs).join (Assign.ofList out.2)) = out.1
  /-- A candidate is determined by its owned part and its trace. -/
  determined : ∀ n, WF n → ∀ g ∈ cands n, ∀ g' ∈ cands n,
    g.restrict (owned n) = g'.restrict (owned n) → trace n g = trace n g' → g = g'
  /-- Among accepted candidates the owned part alone determines the trace. -/
  accept_determined : ∀ n, WF n → ∀ g ∈ cands n, ∀ g' ∈ cands n,
    accept (trace n g) = true → accept (trace n g') = true →
    g.restrict (owned n) = g'.restrict (owned n) → trace n g = trace n g'
  solution : Node Op → Assign → Prop
  accept_iff : ∀ n g, g ∈ cands n → (solution n g ↔ accept (trace n g) = true)

namespace OwnedInstance
open Traced
variable {Op Tau : Type*} [DecidableEq Tau] (I : OwnedInstance Op Tau)

/-- What a row denotes: the owned parts of the candidates with its trace. -/
def rowSet (n : Node Op) (τ : Tau) : Finset Assign :=
  ((I.cands n).filter fun g => I.trace n g = τ).image fun g => g.restrict (I.owned n)

theorem mem_rowSet {n : Node Op} {τ : Tau} {f : Assign} :
    f ∈ I.rowSet n τ ↔ ∃ g ∈ I.cands n, I.trace n g = τ ∧ f = g.restrict (I.owned n) := by
  rw [rowSet, Finset.mem_image]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [Finset.mem_filter] at hg
    exact ⟨g, hg.1, hg.2, rfl⟩
  · rintro ⟨g, hg, hτ, rfl⟩
    exact ⟨g, Finset.mem_filter.mpr ⟨hg, hτ⟩, rfl⟩

theorem dom_of_mem_rowSet {n : Node Op} (hwf : I.WF n) {τ : Tau} {f : Assign}
    (hf : f ∈ I.rowSet n τ) : f.dom = I.owned n := by
  rw [mem_rowSet] at hf
  obtain ⟨g, hg, _, rfl⟩ := hf
  rw [Assign.restrict_dom, I.dom_eq n hwf g hg]
  exact Finset.inter_eq_right.mpr (I.owned_sub n hwf)

theorem rowSet_disjoint_accept {n : Node Op} (hwf : I.WF n) {τ τ' : Tau} (h : τ ≠ τ')
    (hτ : I.accept τ = true) (hτ' : I.accept τ' = true) :
    Disjoint (I.rowSet n τ) (I.rowSet n τ') := by
  rw [Finset.disjoint_left]
  intro f hf hf'
  rw [mem_rowSet] at hf hf'
  obtain ⟨g, hg, hgτ, rfl⟩ := hf
  obtain ⟨g', hg', hgτ', hfg'⟩ := hf'
  apply h
  rw [← hgτ, ← hgτ']
  exact I.accept_determined n hwf g hg g' hg' (by rw [hgτ]; exact hτ) (by rw [hgτ']; exact hτ')
    hfg'

theorem children_pairwise {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs)) :
    cs.Pairwise fun c c' => Disjoint (I.owned c) (I.owned c') :=
  List.pairwise_map.mp (I.children_owned_disjoint op cs hwf)

theorem children_pairwise_wf {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs)) :
    cs.Pairwise fun c c' => I.WF c ∧ I.WF c' ∧ Disjoint (I.owned c) (I.owned c') :=
  List.Pairwise.imp_of_mem
    (fun {c c'} hc hc' h => ⟨I.wf_children op cs hwf c hc, I.wf_children op cs hwf c' hc', h⟩)
    (I.children_pairwise hwf)

/-- The children's tables, as the induction hypothesis provides them. -/
def TablesSem (tables : List (Table Tau)) (cs : List (Node Op)) : Prop :=
  List.Forall₂ (fun T c => TableSem T (I.rowSet c) ∧ (T.map Prod.fst).Nodup) tables cs

theorem rows_sem :
    ∀ {rows : List (Tau × Expr)} {tables : List (Table Tau)} {cs : List (Node Op)},
      List.Forall₂ (· ∈ ·) rows tables → I.TablesSem tables cs →
      List.Forall₂ (fun r c => Sem r.2 (I.rowSet c r.1)) rows cs
  | [], [], [], _, _ => List.Forall₂.nil
  | [], [], _ :: _, _, hT => nomatch hT
  | [], _ :: _, _, hr, _ => nomatch hr
  | _ :: _, [], _, hr, _ => nomatch hr
  | _ :: _, _ :: _, [], _, hT => nomatch hT
  | r :: rows, T :: tables, c :: cs, hr, hT => by
    rw [List.forall₂_cons] at hr
    rw [TablesSem, List.forall₂_cons] at hT
    refine List.Forall₂.cons ?_ (rows_sem hr.2 hT.2)
    have h := hT.1.1 r.1
    rw [rowExpr_of_mem hT.1.2 (show (r.1, r.2) ∈ T from hr.1)] at h
    exact h

theorem joined_sem {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {tables : List (Table Tau)} (hT : I.TablesSem tables cs) {rows : List (Tau × Expr)}
    (hrows : List.Forall₂ (· ∈ ·) rows tables) :
    Sem (joined rows) (joinedSet (List.zipWith (fun r c => I.rowSet c r.1) rows cs)) := by
  have hrs := I.rows_sem hrows hT
  apply Sem.joined
  · exact forall₂_zipWith_of_forall₂ (fun (r : Tau × Expr) (c : Node Op) => I.rowSet c r.1)
      (fun _ _ h => h) hrs
  · apply pairwise_zipWith_right
      (P := fun c c' => I.WF c ∧ I.WF c' ∧ Disjoint (I.owned c) (I.owned c')) _ _
      rows cs (I.children_pairwise_wf hwf)
    intro r r' c c' ⟨hc, hc', hcc'⟩ f hf g hg
    rw [I.dom_of_mem_rowSet hc hf, I.dom_of_mem_rowSet hc' hg]
    exact hcc'

/-- A variable of a join of owned parts is owned by one of the children. -/
theorem mem_dom_joinAll {cs : List (Node Op)} (hcs : ∀ c ∈ cs, I.WF c) {rows : List (Tau × Expr)}
    {fs : List Assign}
    (hfs : List.Forall₂ (· ∈ ·) fs (List.zipWith (fun r c => I.rowSet c r.1) rows cs)) {x : Var}
    (hx : x ∈ (Assign.joinAll fs).dom) : ∃ c ∈ cs, x ∈ I.owned c := by
  unfold Assign.joinAll at hx
  have hsub := Assign.dom_foldl_join_subset fs Assign.empty hx
  rw [Assign.empty_dom, Finset.empty_union] at hsub
  obtain ⟨D, hD, hxD⟩ := mem_foldr_union _ hsub
  rw [List.mem_map] at hD
  obtain ⟨g, hg, rfl⟩ := hD
  obtain ⟨A, hA, hgA⟩ := forall₂_mem_left hfs hg
  obtain ⟨r, c, hc, rfl⟩ := mem_zipWith_right _ rows cs hA
  refine ⟨c, hc, ?_⟩
  rw [← I.dom_of_mem_rowSet (hcs c hc) hgA]
  exact hxD

/-- The denotation of one item: the owned parts of one candidate per child with the rows'
    traces, joined with the leaves of one `step` output. -/
def itemSet (cs : List (Node Op)) (rows : List (Tau × Expr)) (out : Tau × List (Var × Val)) :
    Finset Assign :=
  (joinedSet (List.zipWith (fun r c => I.rowSet c r.1) rows cs)).image fun f =>
    f.join (Assign.ofList out.2)

theorem item_sem {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {tables : List (Table Tau)} (hT : I.TablesSem tables cs) {rows : List (Tau × Expr)}
    (hrows : List.Forall₂ (· ∈ ·) rows tables) {out : Tau × List (Var × Val)}
    (hout : out ∈ I.step op (rows.map Prod.fst)) :
    Sem (Expr.joinLeaves (joined rows) out.2) (I.itemSet cs rows out) := by
  obtain ⟨hnd, hvars⟩ := I.step_leaves op _ out hout
  apply Sem.joinLeaves (I.joined_sem hwf hT hrows) out.2 hnd
  intro f hf q hq hqf
  rw [mem_joinedSet] at hf
  obtain ⟨fs, hfs, rfl⟩ := hf
  obtain ⟨c, hc, hqc⟩ := I.mem_dom_joinAll (I.wf_children op cs hwf) hfs hqf
  have hq_owned : q.1 ∈ I.opOwned op := by
    rw [← hvars, List.mem_toFinset]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  exact Finset.disjoint_left.mp (I.opOwned_disjoint op cs hwf c hc) hq_owned
    (I.owned_sub c (I.wf_children op cs hwf c hc) hqc)

theorem ofList_dom_owned {op : Op} {taus : List Tau} {out : Tau × List (Var × Val)}
    (hout : out ∈ I.step op taus) : (Assign.ofList out.2).dom = I.opOwned op := by
  obtain ⟨hnd, hvars⟩ := I.step_leaves op taus out hout
  rw [Assign.ofList_dom _ hnd, hvars]

/-- A member of an item restricts to the output's leaves on the operation's own variables. -/
theorem restrict_opOwned_of_mem_itemSet {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {rows : List (Tau × Expr)} {out : Tau × List (Var × Val)}
    (hout : out ∈ I.step op (rows.map Prod.fst)) {f : Assign} (hf : f ∈ I.itemSet cs rows out) :
    f.restrict (I.opOwned op) = Assign.ofList out.2 := by
  rw [itemSet, Finset.mem_image] at hf
  obtain ⟨a, ha, rfl⟩ := hf
  rw [mem_joinedSet] at ha
  obtain ⟨fs, hfs, rfl⟩ := ha
  have hd : Disjoint (Assign.joinAll fs).dom (Assign.ofList out.2).dom := by
    rw [I.ofList_dom_owned hout, Finset.disjoint_left]
    intro x hx hxo
    obtain ⟨c, hc, hxc⟩ := I.mem_dom_joinAll (I.wf_children op cs hwf) hfs hx
    exact Finset.disjoint_left.mp (I.opOwned_disjoint op cs hwf c hc) hxo
      (I.owned_sub c (I.wf_children op cs hwf c hc) hxc)
  rw [← I.ofList_dom_owned hout]
  exact Assign.join_restrict_right hd

/-- The owned parts of one candidate per child. -/
def ownedParts (cs : List (Node Op)) (gs : List Assign) : List Assign :=
  List.zipWith (fun g c => g.restrict (I.owned c)) gs cs

/-- One assignment per zipped row set is the owned part of one candidate per child with the
    rows' traces. -/
theorem cand_of_zip :
    ∀ (rows : List (Tau × Expr)) (cs : List (Node Op)) (fs : List Assign),
      rows.length = cs.length →
      List.Forall₂ (· ∈ ·) fs (List.zipWith (fun r c => I.rowSet c r.1) rows cs) →
      ∃ gs : List Assign, List.Forall₂ (fun g c => g ∈ I.cands c) gs cs ∧
        rows.map Prod.fst = List.zipWith I.trace cs gs ∧ fs = I.ownedParts cs gs
  | [], [], fs, _, hfs => by
    cases hfs
    exact ⟨[], List.Forall₂.nil, rfl, rfl⟩
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | r :: rows, c :: cs, fs, hlen, hfs => by
    rw [List.zipWith_cons_cons] at hfs
    cases hfs with
    | cons hf hfs =>
      rename_i f fs
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [mem_rowSet] at hf
      obtain ⟨g, hg, hτ, rfl⟩ := hf
      obtain ⟨gs, h1, h2, h3⟩ := cand_of_zip rows cs fs hlen hfs
      refine ⟨g :: gs, List.Forall₂.cons hg h1, ?_, ?_⟩
      · rw [List.map_cons, List.zipWith_cons_cons, h2, hτ]
      · rw [ownedParts, List.zipWith_cons_cons, h3]
        rfl

/-- For one candidate per child there is a tuple of rows, one from each table, with their
    traces, whose row sets hold the candidates' owned parts. -/
theorem exists_rows {tables : List (Table Tau)} {cs : List (Node Op)} (hT : I.TablesSem tables cs) :
    ∀ {gs : List Assign}, List.Forall₂ (fun g c => g ∈ I.cands c) gs cs →
      ∃ rows : List (Tau × Expr), List.Forall₂ (· ∈ ·) rows tables ∧
        rows.map Prod.fst = List.zipWith I.trace cs gs ∧
        List.Forall₂ (· ∈ ·) (I.ownedParts cs gs)
          (List.zipWith (fun r c => I.rowSet c r.1) rows cs) := by
  induction hT with
  | nil =>
    intro gs hgs
    cases hgs
    exact ⟨[], List.Forall₂.nil, rfl, List.Forall₂.nil⟩
  | @cons T c tables cs hTc _ ih =>
    intro gs hgs
    cases hgs with
    | @cons g _ gs _ hg hgs =>
      obtain ⟨rows, h1, h2, h3⟩ := ih hgs
      have hfr : g.restrict (I.owned c) ∈ I.rowSet c (I.trace c g) := by
        rw [mem_rowSet]
        exact ⟨g, hg, rfl, rfl⟩
      have hne : rowExpr T (I.trace c g) ≠ .empty :=
        Sem.ne_empty (hTc.1 (I.trace c g)) ⟨_, hfr⟩
      refine ⟨(I.trace c g, rowExpr T (I.trace c g)) :: rows,
        List.Forall₂.cons (mem_of_rowExpr_ne hne) h1, ?_, ?_⟩
      · rw [List.map_cons, List.zipWith_cons_cons, h2]
      · rw [ownedParts, List.zipWith_cons_cons, List.zipWith_cons_cons]
        exact List.Forall₂.cons hfr h3

/-! ### The owned part of a candidate built from the children's -/

theorem ownedParts_map_dom :
    ∀ {gs : List Assign} {cs : List (Node Op)}, List.Forall₂ (fun g c => g ∈ I.cands c) gs cs →
      (∀ c ∈ cs, I.WF c) → (I.ownedParts cs gs).map Assign.dom = cs.map I.owned
  | [], [], _, _ => rfl
  | g :: gs, c :: cs, hgs, hcs => by
    rw [List.forall₂_cons] at hgs
    have ih := ownedParts_map_dom hgs.2 (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
    rw [ownedParts] at ih
    rw [ownedParts, List.zipWith_cons_cons, List.map_cons, List.map_cons,
      Assign.restrict_dom, I.dom_eq c (hcs c (List.mem_cons_self ..)) g hgs.1,
      Finset.inter_eq_right.mpr (I.owned_sub c (hcs c (List.mem_cons_self ..))), ih]

theorem mem_dom_cands_of_mem_dom_joinAll {gs : List Assign} {cs : List (Node Op)}
    (hgs : List.Forall₂ (fun g c => g ∈ I.cands c) gs cs) (hcs : ∀ c ∈ cs, I.WF c) {x : Var}
    (hx : x ∈ (Assign.joinAll gs).dom) : ∃ c ∈ cs, x ∈ I.dom c := by
  rw [Assign.joinAll_dom] at hx
  obtain ⟨D, hD, hxD⟩ := mem_foldr_union _ hx
  rw [List.mem_map] at hD
  obtain ⟨g, hg, rfl⟩ := hD
  obtain ⟨c, hc, hgc⟩ := forall₂_mem_left hgs hg
  refine ⟨c, hc, ?_⟩
  rw [← I.dom_eq c (hcs c hc) g hgc]
  exact hxD

theorem leaves_compat_joinAll {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {gs : List Assign} (hgs : List.Forall₂ (fun g c => g ∈ I.cands c) gs cs)
    {out : Tau × List (Var × Val)} (hout : out ∈ I.step op (List.zipWith I.trace cs gs)) :
    Disjoint (Assign.joinAll gs).dom (Assign.ofList out.2).dom := by
  rw [I.ofList_dom_owned hout, Finset.disjoint_left]
  intro x hx hxo
  obtain ⟨c, hc, hxc⟩ := I.mem_dom_cands_of_mem_dom_joinAll hgs (I.wf_children op cs hwf) hx
  exact Finset.disjoint_left.mp (I.opOwned_disjoint op cs hwf c hc) hxo hxc

theorem exists_ownedPart :
    ∀ {gs : List Assign} {cs : List (Node Op)}, List.Forall₂ (fun g c => g ∈ I.cands c) gs cs →
      ∀ c ∈ cs, ∃ g ∈ gs, g ∈ I.cands c ∧ g.restrict (I.owned c) ∈ I.ownedParts cs gs
  | [], [], _, _, hc => nomatch hc
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h
  | g :: gs, c' :: cs, h, c, hc => by
    rw [List.forall₂_cons] at h
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc
    · refine ⟨g, List.mem_cons_self .., h.1, ?_⟩
      rw [ownedParts, List.zipWith_cons_cons]
      exact List.mem_cons_self ..
    · obtain ⟨g', hg', hgc, hmem⟩ := exists_ownedPart h.2 c hc
      refine ⟨g', List.mem_cons_of_mem _ hg', hgc, ?_⟩
      rw [ownedParts, List.zipWith_cons_cons]
      exact List.mem_cons_of_mem _ hmem

theorem ownedParts_pairwise_compat {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {gs : List Assign} (hgs : List.Forall₂ (fun g c => g ∈ I.cands c) gs cs) :
    (I.ownedParts cs gs).Pairwise Assign.Compat := by
  have h1 : ((I.ownedParts cs gs).map Assign.dom).Pairwise Disjoint := by
    rw [I.ownedParts_map_dom hgs (I.wf_children op cs hwf)]
    exact I.children_owned_disjoint op cs hwf
  rw [List.pairwise_map] at h1
  exact h1.imp fun h => Assign.compat_of_disjoint h

/-- The owned part of a candidate built from one candidate per child is the join of the
    children's owned parts with the operation's leaves. -/
theorem restrict_owned_mk {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {gs : List Assign} (hgs : List.Forall₂ (fun g c => g ∈ I.cands c) gs cs)
    (hcompat : gs.Pairwise Assign.Compat) {out : Tau × List (Var × Val)}
    (hout : out ∈ I.step op (List.zipWith I.trace cs gs)) :
    ((Assign.joinAll gs).join (Assign.ofList out.2)).restrict (I.owned (.mk op cs)) =
      (Assign.joinAll (I.ownedParts cs gs)).join (Assign.ofList out.2) := by
  have hcs : ∀ c ∈ cs, I.WF c := I.wf_children op cs hwf
  have hE : (Assign.ofList out.2).dom = I.opOwned op := I.ofList_dom_owned hout
  have hLE : Disjoint (Assign.joinAll gs).dom (Assign.ofList out.2).dom :=
    I.leaves_compat_joinAll hwf hgs hout
  have hown := I.owned_mk op cs hwf
  -- the owned parts' join has the children's owned variables as its domain
  have hFdom : (Assign.joinAll (I.ownedParts cs gs)).dom = (cs.map I.owned).foldr (· ∪ ·) ∅ := by
    rw [Assign.joinAll_dom, I.ownedParts_map_dom hgs hcs]
  have hFE : Disjoint (Assign.joinAll (I.ownedParts cs gs)).dom (Assign.ofList out.2).dom := by
    rw [hFdom, hE, Finset.disjoint_left]
    intro x hx hxo
    obtain ⟨D, hD, hxD⟩ := mem_foldr_union _ hx
    rw [List.mem_map] at hD
    obtain ⟨c, hc, rfl⟩ := hD
    exact Finset.disjoint_left.mp (I.opOwned_disjoint op cs hwf c hc) hxo
      (I.owned_sub c (hcs c hc) hxD)
  -- every owned variable is a variable of the built candidate
  have hsub : I.owned (.mk op cs) ⊆ ((Assign.joinAll gs).join (Assign.ofList out.2)).dom := by
    rw [Assign.join_dom_eq, hown, hE]
    intro x hx
    rw [Finset.mem_union] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inr hx
    · left
      obtain ⟨D, hD, hxD⟩ := mem_foldr_union _ hx
      rw [List.mem_map] at hD
      obtain ⟨c, hc, rfl⟩ := hD
      obtain ⟨g, hg, hgc⟩ := forall₂_mem_left hgs.flip hc
      rw [Assign.joinAll_dom]
      apply mem_foldr_union_of_mem (gs.map Assign.dom) (List.mem_map.mpr ⟨g, hg, rfl⟩)
      rw [I.dom_eq c (hcs c hc) g hgc]
      exact I.owned_sub c (hcs c hc) hxD
  apply Assign.ext_of_dom_eq
  · rw [Assign.restrict_dom, Finset.inter_eq_right.mpr hsub, Assign.join_dom_eq, hFdom, hE, hown,
      Finset.union_comm]
  · intro p hp
    rw [Assign.mem_restrict_val] at hp
    obtain ⟨hp, hpo⟩ := hp
    rw [Assign.join_val hLE, Finset.mem_union, Assign.joinAll_val_of_compat hcompat] at hp
    rw [Assign.join_val hFE, Finset.mem_union]
    rcases hp with hp | hp
    · -- a pair of some child's candidate, on an owned variable: in that child's owned part
      left
      obtain ⟨V, hV, hpV⟩ := mem_foldr_union _ hp
      rw [List.mem_map] at hV
      obtain ⟨g, hg, rfl⟩ := hV
      obtain ⟨c, hc, hgc⟩ := forall₂_mem_left hgs hg
      -- the variable is owned by some child `c'`
      have hpo' : ∃ c' ∈ cs, p.1 ∈ I.owned c' := by
        rw [hown, Finset.mem_union] at hpo
        rcases hpo with hpo | hpo
        · exfalso
          exact Finset.disjoint_left.mp (I.opOwned_disjoint op cs hwf c hc) hpo
            (by rw [← I.dom_eq c (hcs c hc) g hgc]; exact Assign.fst_mem_dom hpV)
        · obtain ⟨D, hD, hpD⟩ := mem_foldr_union _ hpo
          rw [List.mem_map] at hD
          obtain ⟨c', hc', rfl⟩ := hD
          exact ⟨c', hc', hpD⟩
      obtain ⟨c', hc', hpc'⟩ := hpo'
      -- `c'`'s candidate assigns that variable too, and agrees with `g` on it
      obtain ⟨g', hg', hgc', hmem⟩ := I.exists_ownedPart hgs c' hc'
      have hpd' : p.1 ∈ g'.dom := by
        rw [I.dom_eq c' (hcs c' hc') g' hgc']
        exact I.owned_sub c' (hcs c' hc') hpc'
      rw [Assign.dom, Finset.mem_image] at hpd'
      obtain ⟨q, hq, hqp⟩ := hpd'
      have hcompat' : Assign.Compat g g' := Assign.compat_of_pairwise hcompat g hg g' hg'
      have hpq : p = q := hcompat' p hpV q hq hqp.symm
      rw [Assign.joinAll_val_of_compat (I.ownedParts_pairwise_compat hwf hgs)]
      apply mem_foldr_union_of_mem _ (List.mem_map.mpr ⟨g'.restrict (I.owned c'), hmem, rfl⟩)
      rw [Assign.mem_restrict_val]
      refine ⟨?_, hpc'⟩
      rw [hpq]
      exact hq
    · right
      exact hp

/-- Members of an item are owned parts of candidates of the node with the output's trace. -/
theorem mem_rowSet_of_mem_itemSet {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {tables : List (Table Tau)} (hT : I.TablesSem tables cs) {rows : List (Tau × Expr)}
    (hrows : List.Forall₂ (· ∈ ·) rows tables) {out : Tau × List (Var × Val)}
    (hout : out ∈ I.step op (rows.map Prod.fst)) {f : Assign} (hf : f ∈ I.itemSet cs rows out) :
    ∃ gs : List Assign, List.Forall₂ (fun g c => g ∈ I.cands c) gs cs ∧
      rows.map Prod.fst = List.zipWith I.trace cs gs ∧
      (Assign.joinAll gs).join (Assign.ofList out.2) ∈ I.cands (.mk op cs) ∧
      I.trace (.mk op cs) ((Assign.joinAll gs).join (Assign.ofList out.2)) = out.1 ∧
      f = ((Assign.joinAll gs).join (Assign.ofList out.2)).restrict (I.owned (.mk op cs)) := by
  have hlen : tables.length = cs.length := List.Forall₂.length_eq hT
  rw [itemSet, Finset.mem_image] at hf
  obtain ⟨a, ha, rfl⟩ := hf
  rw [mem_joinedSet] at ha
  obtain ⟨fs, hfs, rfl⟩ := ha
  obtain ⟨gs, hgs, htr, rfl⟩ :=
    I.cand_of_zip rows cs fs ((List.Forall₂.length_eq hrows).trans hlen) hfs
  rw [htr] at hout
  have hcompat := I.step_compat op cs gs hwf hgs out hout
  refine ⟨gs, hgs, htr, (I.cand_iff op cs hwf _).mpr ⟨gs, hgs, hcompat, out, hout, rfl⟩,
    I.trace_mk op cs gs out hwf hgs hout, ?_⟩
  rw [I.restrict_owned_mk hwf hgs hcompat hout]

/-- Items of one tuple with different leaves are disjoint. -/
theorem itemSet_disjoint_of_ne_leaves {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {rows : List (Tau × Expr)} {out out' : Tau × List (Var × Val)}
    (hout : out ∈ I.step op (rows.map Prod.fst)) (hout' : out' ∈ I.step op (rows.map Prod.fst))
    (hne : Assign.ofList out.2 ≠ Assign.ofList out'.2) :
    Disjoint (I.itemSet cs rows out) (I.itemSet cs rows out') := by
  rw [Finset.disjoint_left]
  intro f hf hf'
  exact hne ((I.restrict_opOwned_of_mem_itemSet hwf hout hf).symm.trans
    (I.restrict_opOwned_of_mem_itemSet hwf hout' hf'))

/-- A candidate built from one candidate per child restricts to each child's candidate on that
    child's variables. -/
theorem restrict_children {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {gs : List Assign} (hgs : List.Forall₂ (fun g c => g ∈ I.cands c) gs cs)
    (hcompat : gs.Pairwise Assign.Compat) {out : Tau × List (Var × Val)}
    (hout : out ∈ I.step op (List.zipWith I.trace cs gs)) :
    List.Forall₂ (fun g c =>
      ((Assign.joinAll gs).join (Assign.ofList out.2)).restrict (I.dom c) = g) gs cs := by
  apply forall₂_imp_mem _ hgs
  intro g hg c hc hgc
  rw [← I.dom_eq c (I.wf_children op cs hwf c hc) g hgc, Assign.restrict_join_of_disjoint_right,
    Assign.restrict_joinAll_mem hcompat hg]
  rw [I.dom_eq c (I.wf_children op cs hwf c hc) g hgc, I.ofList_dom_owned hout]
  exact (I.opOwned_disjoint op cs hwf c hc).symm

theorem forall₂_eq_of_restrict {G : Assign} :
    ∀ {gs gs' : List Assign} {cs : List (Node Op)},
      List.Forall₂ (fun g c => G.restrict (I.dom c) = g) gs cs →
      List.Forall₂ (fun g c => G.restrict (I.dom c) = g) gs' cs → gs = gs'
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, h, _ => nomatch h
  | [], _ :: _, [], _, h' => nomatch h'
  | [], _ :: _, _ :: _, h, _ => nomatch h
  | _ :: _, [], [], h, _ => nomatch h
  | _ :: _, [], _ :: _, _, h' => nomatch h'
  | _ :: _, _ :: _, [], h, _ => nomatch h
  | g :: gs, g' :: gs', c :: cs, h, h' => by
    rw [List.forall₂_cons] at h h'
    rw [forall₂_eq_of_restrict h.2 h'.2, ← h.1, ← h'.1]

/-- Two tuples of children's candidates that build one candidate are the same tuple. -/
theorem cands_eq_of_join_eq {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {gs gs' : List Assign} (hgs : List.Forall₂ (fun g c => g ∈ I.cands c) gs cs)
    (hgs' : List.Forall₂ (fun g c => g ∈ I.cands c) gs' cs)
    (hc : gs.Pairwise Assign.Compat) (hc' : gs'.Pairwise Assign.Compat)
    {out out' : Tau × List (Var × Val)} (hout : out ∈ I.step op (List.zipWith I.trace cs gs))
    (hout' : out' ∈ I.step op (List.zipWith I.trace cs gs'))
    (heq : (Assign.joinAll gs).join (Assign.ofList out.2) =
      (Assign.joinAll gs').join (Assign.ofList out'.2)) : gs = gs' := by
  have h1 := I.restrict_children hwf hgs hc hout
  have h2 := I.restrict_children hwf hgs' hc' hout'
  rw [heq] at h1
  exact I.forall₂_eq_of_restrict h1 h2

theorem rows_eq_of_map_fst {tables : List (Table Tau)} {cs : List (Node Op)}
    (hT : I.TablesSem tables cs) :
    ∀ {rows rows' : List (Tau × Expr)}, List.Forall₂ (· ∈ ·) rows tables →
      List.Forall₂ (· ∈ ·) rows' tables → rows.map Prod.fst = rows'.map Prod.fst → rows = rows' := by
  induction hT with
  | nil =>
    intro rows rows' h1 h2 _
    cases h1
    cases h2
    rfl
  | cons hTc _ ih =>
    intro rows rows' h1 h2 hm
    cases h1 with
    | cons hr h1 =>
      cases h2 with
      | cons hr' h2 =>
        rw [List.map_cons, List.map_cons, List.cons.injEq] at hm
        rw [eq_of_mem_of_fst_eq hTc.2 hr hr' hm.1, ih h1 h2 hm.2]

/-- Two tuples of rows whose items share an owned part and a trace are the same tuple. -/
theorem rows_eq_of_mem_itemSet {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {tables : List (Table Tau)} (hT : I.TablesSem tables cs) {rows rows' : List (Tau × Expr)}
    (hrows : List.Forall₂ (· ∈ ·) rows tables) (hrows' : List.Forall₂ (· ∈ ·) rows' tables)
    {out out' : Tau × List (Var × Val)} (hout : out ∈ I.step op (rows.map Prod.fst))
    (hout' : out' ∈ I.step op (rows'.map Prod.fst)) (hτ : out.1 = out'.1) {f : Assign}
    (hf : f ∈ I.itemSet cs rows out) (hf' : f ∈ I.itemSet cs rows' out') : rows = rows' := by
  obtain ⟨gs, hgs, htr, hg, hgτ, hfg⟩ := I.mem_rowSet_of_mem_itemSet hwf hT hrows hout hf
  obtain ⟨gs', hgs', htr', hg', hgτ', hfg'⟩ := I.mem_rowSet_of_mem_itemSet hwf hT hrows' hout' hf'
  have hout2 : out ∈ I.step op (List.zipWith I.trace cs gs) := by rw [← htr]; exact hout
  have hout2' : out' ∈ I.step op (List.zipWith I.trace cs gs') := by rw [← htr']; exact hout'
  have heq := I.determined _ hwf _ hg _ hg' (hfg.symm.trans hfg') (by rw [hgτ, hgτ', hτ])
  have hgs_eq : gs = gs' := I.cands_eq_of_join_eq hwf hgs hgs'
    (I.step_compat op cs gs hwf hgs out hout2) (I.step_compat op cs gs' hwf hgs' out' hout2')
    hout2 hout2' heq
  subst hgs_eq
  exact I.rows_eq_of_map_fst hT hrows hrows' (htr.trans htr'.symm)

/-- Claim 1, one step: the children's tables give the node's table. -/
theorem stepNode_sound {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {tables : List (Table Tau)} (hT : I.TablesSem tables cs) :
    TableSem (stepNode I.toTraced op tables) (I.rowSet (.mk op cs)) := by
  rw [stepNode_eq_foldl]
  have hmem : ∀ it, it ∈ (tuples tables).flatMap (rowItems I.toTraced op) ↔
      ∃ rows, List.Forall₂ (· ∈ ·) rows tables ∧
        ∃ out ∈ I.step op (rows.map Prod.fst),
          it = (out.1, Expr.joinLeaves (joined rows) out.2) := by
    intro it
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨rows, hrows, hit⟩
      rw [rowItems, List.mem_map] at hit
      obtain ⟨out, hout, rfl⟩ := hit
      exact ⟨rows, mem_tuples.mp hrows, out, hout, rfl⟩
    · rintro ⟨rows, hrows, out, hout, rfl⟩
      exact ⟨rows, mem_tuples.mpr hrows, List.mem_map.mpr ⟨out, hout, rfl⟩⟩
  have hden : ∀ rows, List.Forall₂ (· ∈ ·) rows tables → ∀ out ∈ I.step op (rows.map Prod.fst),
      denot (Expr.joinLeaves (joined rows) out.2) = I.itemSet cs rows out :=
    fun rows hrows out hout => Sem.denot_eq (I.item_sem hwf hT hrows hout)
  have hcand : ∀ rows, List.Forall₂ (· ∈ ·) rows tables → ∀ out ∈ I.step op (rows.map Prod.fst),
      ∀ f ∈ I.itemSet cs rows out, f ∈ I.rowSet (.mk op cs) out.1 := by
    intro rows hrows out hout f hf
    obtain ⟨gs, _, _, hg, hgτ, hfg⟩ := I.mem_rowSet_of_mem_itemSet hwf hT hrows hout hf
    rw [mem_rowSet]
    exact ⟨_, hg, hgτ, hfg⟩
  have hset : ∀ τ, itemsSet (fun it => denot it.2) ((tuples tables).flatMap (rowItems I.toTraced op)) τ
      = I.rowSet (.mk op cs) τ := by
    intro τ
    ext f
    rw [mem_itemsSet]
    constructor
    · rintro ⟨it, hit, hτ, hf⟩
      rw [hmem] at hit
      obtain ⟨rows, hrows, out, hout, rfl⟩ := hit
      rw [hden rows hrows out hout] at hf
      have h := hcand rows hrows out hout f hf
      rw [← hτ]
      exact h
    · intro hf
      rw [mem_rowSet] at hf
      obtain ⟨g, hg, hτ, rfl⟩ := hf
      obtain ⟨gs, hgs, hcompat, out, hout, rfl⟩ := (I.cand_iff op cs hwf g).mp hg
      obtain ⟨rows, hrows, htr, hfs⟩ := I.exists_rows hT hgs
      have hout' : out ∈ I.step op (rows.map Prod.fst) := by rw [htr]; exact hout
      refine ⟨(out.1, Expr.joinLeaves (joined rows) out.2), ?_, ?_, ?_⟩
      · rw [hmem]
        exact ⟨rows, hrows, out, hout', rfl⟩
      · show out.1 = τ
        rw [← hτ, I.trace_mk op cs gs out hwf hgs hout]
      · show _ ∈ denot (Expr.joinLeaves (joined rows) out.2)
        rw [hden rows hrows out hout', itemSet, Finset.mem_image]
        refine ⟨Assign.joinAll (I.ownedParts cs gs), (mem_joinedSet _ _).mpr ⟨_, hfs, rfl⟩, ?_⟩
        rw [I.restrict_owned_mk hwf hgs hcompat hout]
  have key := TableSem.foldl_unionInto' (Dn := I.owned (.mk op cs)) (fun it => denot it.2)
    ((tuples tables).flatMap (rowItems I.toTraced op)) (T := []) (S := fun _ => ∅)
    (fun _ => Sem.empty) ?_ ?_ ?_ ?_ ?_
  · intro τ
    have h := key τ
    simp only [Finset.empty_union] at h
    rw [hset τ] at h
    exact h
  · intro it hit
    rw [hmem] at hit
    obtain ⟨rows, hrows, out, hout, rfl⟩ := hit
    show Sem (Expr.joinLeaves (joined rows) out.2) (denot (Expr.joinLeaves (joined rows) out.2))
    rw [hden rows hrows out hout]
    exact I.item_sem hwf hT hrows hout
  · apply pairwise_flatMap_of
    · intro rows hrows
      have hrows' := mem_tuples.mp hrows
      rw [rowItems, List.pairwise_map]
      have hs : (I.step op (rows.map Prod.fst)).Pairwise
          (fun o o' => Assign.ofList o.2 ≠ Assign.ofList o'.2) :=
        List.pairwise_map.mp (I.step_nodup op (rows.map Prod.fst))
      refine List.Pairwise.imp_of_mem ?_ hs
      intro o o' ho ho' hne _
      show Disjoint (denot (Expr.joinLeaves (joined rows) o.2))
        (denot (Expr.joinLeaves (joined rows) o'.2))
      rw [hden rows hrows' o ho, hden rows hrows' o' ho']
      exact I.itemSet_disjoint_of_ne_leaves hwf ho ho' hne
    · have hnd : (tuples tables).Pairwise (· ≠ ·) := by
        apply nodup_tuples
        intro T hT'
        obtain ⟨c, _, hc⟩ := forall₂_mem_left hT hT'
        exact hc.2.of_map Prod.fst
      refine List.Pairwise.imp_of_mem ?_ hnd
      intro rows rows' hr hr' hne a ha b hb hab
      rw [rowItems, List.mem_map] at ha hb
      obtain ⟨o, ho, rfl⟩ := ha
      obtain ⟨o', ho', rfl⟩ := hb
      show Disjoint (denot (Expr.joinLeaves (joined rows) o.2))
        (denot (Expr.joinLeaves (joined rows') o'.2))
      rw [hden rows (mem_tuples.mp hr) o ho, hden rows' (mem_tuples.mp hr') o' ho']
      rw [Finset.disjoint_left]
      intro f hf hf'
      exact hne (I.rows_eq_of_mem_itemSet hwf hT (mem_tuples.mp hr) (mem_tuples.mp hr') ho ho' hab
        hf hf')
  · intro it _
    exact Finset.disjoint_empty_left _
  · intro it hit f hf
    rw [hmem] at hit
    obtain ⟨rows, hrows, out, hout, rfl⟩ := hit
    change f ∈ denot (Expr.joinLeaves (joined rows) out.2) at hf
    rw [hden rows hrows out hout] at hf
    exact I.dom_of_mem_rowSet hwf (hcand rows hrows out hout f hf)
  · intro τ f hf
    exact absurd hf (Finset.notMem_empty f)

end OwnedInstance

namespace OwnedInstance
variable {Op Tau : Type*} [DecidableEq Tau]

mutual
/-- Claim 1 at every node: the table of `run` denotes the owned parts of the candidates by
    trace, with distinct traces. -/
theorem run_sound (I : OwnedInstance Op Tau) :
    ∀ n : Node Op, I.WF n →
      Traced.TableSem (Traced.run I.toTraced n) (I.rowSet n) ∧
        ((Traced.run I.toTraced n).map Prod.fst).Nodup
  | .mk op cs, hwf => by
    rw [Traced.run]
    exact ⟨I.stepNode_sound hwf (runList_sound I cs (I.wf_children op cs hwf)),
      Traced.stepNode_nodup _ _ _⟩
theorem runList_sound (I : OwnedInstance Op Tau) :
    ∀ cs : List (Node Op), (∀ c ∈ cs, I.WF c) → I.TablesSem (Traced.runList I.toTraced cs) cs
  | [], _ => List.Forall₂.nil
  | c :: cs, hcs => by
    rw [Traced.runList]
    exact List.Forall₂.cons (run_sound I c (hcs c (List.mem_cons_self ..)))
      (runList_sound I cs fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
end

end OwnedInstance

/-- Claim 1 at the root, for instances with shared variables: on a well-formed construction the
    DP's output denotes exactly the owned parts of the accepted candidates. -/
theorem OwnedInstance.solve_sound {Op Tau : Type*} [DecidableEq Tau] (I : OwnedInstance Op Tau)
    {n : Node Op} (hwf : I.WF n) :
    Sem (I.toTraced.solve n)
      (((I.cands n).filter fun g => I.accept (I.trace n g) = true).image fun g =>
        g.restrict (I.owned n)) := by
  obtain ⟨hT, hnd⟩ := I.run_sound n hwf
  unfold Traced.solve
  have h := Traced.Sem.foldl_accept' (Dn := I.owned n) I.toTraced (I.rowSet n)
    (fun τ τ' hne hτ hτ' => I.rowSet_disjoint_accept hwf hne hτ hτ')
    (fun τ f hf => I.dom_of_mem_rowSet hwf hf)
    (Traced.run I.toTraced n) .empty ∅ Sem.empty hnd
    (fun row hr => by
      have := hT row.1
      rwa [Traced.rowExpr_of_mem hnd (show (row.1, row.2) ∈ _ from hr)] at this)
    (fun _ _ _ => Finset.disjoint_empty_left _) (fun f hf => absurd hf (Finset.notMem_empty f))
  rw [Finset.empty_union] at h
  have hset : Traced.acceptedSet I.toTraced (I.rowSet n) (Traced.run I.toTraced n) =
      ((I.cands n).filter fun g => I.accept (I.trace n g) = true).image fun g =>
        g.restrict (I.owned n) := by
    ext f
    rw [Traced.mem_acceptedSet, Finset.mem_image]
    constructor
    · rintro ⟨row, _, ha, hf⟩
      rw [OwnedInstance.mem_rowSet] at hf
      obtain ⟨g, hg, hτ, rfl⟩ := hf
      exact ⟨g, Finset.mem_filter.mpr ⟨hg, by rw [hτ]; exact ha⟩, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      rw [Finset.mem_filter] at hg
      have hfr : g.restrict (I.owned n) ∈ I.rowSet n (I.trace n g) := by
        rw [OwnedInstance.mem_rowSet]
        exact ⟨g, hg.1, rfl, rfl⟩
      have hne := Sem.ne_empty (hT (I.trace n g)) ⟨_, hfr⟩
      exact ⟨(I.trace n g, Traced.rowExpr (Traced.run I.toTraced n) (I.trace n g)),
        Traced.mem_of_rowExpr_ne hne, hg.2, hfr⟩
  rw [hset] at h
  exact h

end Formalism
