/-!
# The one scheme and its two theorems

Model of `explore/hylo/src/lib.rs`. STATUS: NOT YET CHECKED BY LEAN (no toolchain in the
authoring environment). Proof sketches are given where they are routine; `sorry` elsewhere.

* `Shape`   = a lawful functor `F`.
* `Plan`    = a coalgebra `c : A → F A`. Its obligation is `IsRecursive`.
* `Algebra` = an algebra `a : F B → B`. Its obligations are the carrier's laws.
* `hylo a c` = the unique solution of `h = a ∘ map h ∘ c`.
-/
import Mathlib

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
  -- hom ∘ h = hom ∘ a ∘ map h ∘ c = a' ∘ map hom ∘ map h ∘ c = a' ∘ map (hom ∘ h) ∘ c
  unfold Solves
  have hh := hylo_solves a c hc
  unfold Solves at hh
  conv_lhs => rw [hh]
  unfold IsAlgHom at hab
  rw [← Function.comp_assoc, ← Function.comp_assoc, hab]
  simp [Function.comp_assoc, LawfulFunctor.comp_map]

/-- Well-foundedness gives recursiveness (Adámek, Lücke, Milius 2007, for finitary set functors).
    This is how a concrete plan discharges its obligation: exhibit a measure that `c` decreases. -/
theorem isRecursive_of_wellFounded (c : α → F α) (r : α → α → Prop) (hr : WellFounded r)
    (hdec : ∀ x, ∀ y ∈ (Functor.map (fun y => y) (c x) : F α) |>.toListOf, r y x) :
    IsRecursive c := by
  sorry
-- NOTE: the membership `y ∈ c x` needs a `Traversable`/`Foldable` instance on `F` to state;
-- `toListOf` is a placeholder for that. Fix on first build.

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

/-- Scan over any split equals the sequential prefix products. -/
theorem scan_eq_prefixes {M : Type} [Monoid M] (t : LeafTree M) :
    t.scan.2 = prefixes t.flatten := by
  sorry

end Hylo
