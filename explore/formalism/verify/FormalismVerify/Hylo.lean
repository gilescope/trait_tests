import Mathlib
/-!
# The one scheme and its two theorems

Model of `explore/hylo/src/lib.rs`. Checked by `lake build` in CI (`+verify` in the Earthfile).

* `Shape`   = a lawful functor `F`.
* `Plan`    = a coalgebra `c : A → F A`. Its obligation is `IsRecursive`.
* `Algebra` = an algebra `a : F B → B`. Its obligations are the carrier's laws.
* `hylo a c` = the unique solution of `h = a ∘ map h ∘ c`.
-/

namespace Hylo

variable {F : Type → Type} [Functor F] [LawfulFunctor F]

/-- The hylo equation for a candidate solution `h`. -/
def Solves (a : F β → β) (c : α → F α) (h : α → β) : Prop :=
  h = a ∘ Functor.map h ∘ c

/-- A coalgebra is recursive when the hylo equation has exactly one solution for every algebra
    (Capretta, Uustalu, Vene 2006). This is the plan's only obligation and it is Knuth's finiteness:
    every unfolding bottoms out, whatever is folded over it. -/
def IsRecursive (c : α → F α) : Prop :=
  ∀ (β : Type) (a : F β → β), ∃! h : α → β, Solves a c h

/-- The one scheme. Defined by choice from recursiveness, so it is a specification, not a program;
    the extracted Rust `hylo` refines it. -/
noncomputable def hylo (a : F β → β) (c : α → F α) (hc : IsRecursive c) : α → β :=
  Classical.choose (hc β a)

theorem hylo_solves (a : F β → β) (c : α → F α) (hc : IsRecursive c) :
    Solves a c (hylo a c hc) :=
  (Classical.choose_spec (hc β a)).1

theorem hylo_unique (a : F β → β) (c : α → F α) (hc : IsRecursive c) {h : α → β}
    (hh : Solves a c h) : h = hylo a c hc :=
  (Classical.choose_spec (hc β a)).2 h hh

/-- An F-algebra homomorphism: `hom ∘ a = a' ∘ map hom`. -/
def IsAlgHom (a : F β → β) (a' : F γ → γ) (hom : β → γ) : Prop :=
  hom ∘ a = a' ∘ Functor.map hom

/-- **Fusion.** The query is free: an algebra homomorphism out of the fold commutes with the hylo.
    Baril Lemma 1, GTA Theorem 13 and Goodman Theorem 1 are instances. -/
theorem fusion (a : F β → β) (a' : F γ → γ) (hom : β → γ) (hab : IsAlgHom a a' hom)
    (c : α → F α) (hc : IsRecursive c) :
    hom ∘ hylo a c hc = hylo a' c hc := by
  apply hylo_unique
  unfold Solves
  have hh : hylo a c hc = a ∘ Functor.map (hylo a c hc) ∘ c := hylo_solves a c hc
  have hmap : Functor.map (hom ∘ hylo a c hc) =
      (Functor.map hom ∘ Functor.map (hylo a c hc) : F α → F γ) :=
    funext fun x => LawfulFunctor.comp_map (hylo a c hc) hom x
  calc hom ∘ hylo a c hc
      = hom ∘ (a ∘ Functor.map (hylo a c hc) ∘ c) := congrArg (fun g => hom ∘ g) hh
    _ = (hom ∘ a) ∘ Functor.map (hylo a c hc) ∘ c := rfl
    _ = (a' ∘ Functor.map hom) ∘ Functor.map (hylo a c hc) ∘ c := by rw [hab]
    _ = a' ∘ (Functor.map hom ∘ Functor.map (hylo a c hc)) ∘ c := rfl
    _ = a' ∘ Functor.map (hom ∘ hylo a c hc) ∘ c := by rw [hmap]

/-! ## The homomorphism theorem, for the two sequence shapes in the crate -/

/-- `LeafTreeF`: data at the leaves. A value of this type is one plan's split of a list. -/
inductive LeafTree (M : Type) where
  | leaf : Option M → LeafTree M
  | node : LeafTree M → LeafTree M → LeafTree M

def LeafTree.flatten {M : Type} : LeafTree M → List M
  | .leaf none => []
  | .leaf (some x) => [x]
  | .node l r => l.flatten ++ r.flatten

/-- `ReduceT` in the crate. -/
def LeafTree.reduce {M : Type} [Monoid M] : LeafTree M → M
  | .leaf none => 1
  | .leaf (some x) => x
  | .node l r => l.reduce * r.reduce

/-- **Homomorphism theorem, list case.** Every split (plan) of a list reduces to its product.
    `ReduceL` is `List.prod` by definition, so `reduce_seq = reduce_par` for every monoid. -/
theorem reduce_eq_prod {M : Type} [Monoid M] (t : LeafTree M) :
    t.reduce = t.flatten.prod := by
  induction t with
  | leaf o => cases o <;> simp [LeafTree.reduce, LeafTree.flatten]
  | node l r ihl ihr => simp [LeafTree.reduce, LeafTree.flatten, List.prod_append, ihl, ihr]

/-- Scan, Sklansky's shape, as in `Scan` in the crate. -/
def LeafTree.scan {M : Type} [Monoid M] : LeafTree M → M × List M
  | .leaf none => (1, [])
  | .leaf (some x) => (x, [x])
  | .node l r =>
    let (tl, pl) := l.scan
    let (tr, pr) := r.scan
    (tl * tr, pl ++ pr.map (tl * ·))

/-- Inclusive prefix products of a list. -/
def prefixes {M : Type} [Monoid M] (xs : List M) : List M :=
  (List.range xs.length).map fun i => (xs.take (i + 1)).prod

theorem prefixes_nil {M : Type} [Monoid M] : prefixes ([] : List M) = [] := by
  simp [prefixes]

theorem prefixes_cons {M : Type} [Monoid M] (x : M) (xs : List M) :
    prefixes (x :: xs) = x :: (prefixes xs).map (x * ·) := by
  simp [prefixes, List.range_succ_eq_map, List.map_map, Function.comp_def, List.take_succ_cons,
    List.prod_cons]

/-- Prefix products of a concatenation: the right part is shifted by the left product. This is
    the one fact Sklansky's node needs. -/
theorem prefixes_append {M : Type} [Monoid M] (xs ys : List M) :
    prefixes (xs ++ ys) = prefixes xs ++ (prefixes ys).map (xs.prod * ·) := by
  induction xs with
  | nil => simp [prefixes_nil]
  | cons x xs ih => simp [prefixes_cons, ih, List.map_map, Function.comp_def, mul_assoc]

/-- Scan over any split computes the total and the sequential prefix products. -/
theorem scan_spec {M : Type} [Monoid M] (t : LeafTree M) :
    t.scan = (t.flatten.prod, prefixes t.flatten) := by
  induction t with
  | leaf o => cases o <;> simp [LeafTree.scan, LeafTree.flatten, prefixes_nil, prefixes_cons]
  | node l r ihl ihr =>
    simp [LeafTree.scan, LeafTree.flatten, ihl, ihr, List.prod_append, prefixes_append]

/-- **Homomorphism theorem, scan case.** Scan over any split equals the sequential prefix
    products, so `Scan` is plan-independent for every monoid. -/
theorem scan_eq_prefixes {M : Type} [Monoid M] (t : LeafTree M) :
    t.scan.2 = prefixes t.flatten := by
  rw [scan_spec]

end Hylo
