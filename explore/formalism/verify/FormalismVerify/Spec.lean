/-!
# Specification of the formalism

Hand-written model of `explore/formalism/src/{expr,scheme,semiring}.rs`, after
Baril, Couceiro, Lagerkvist, *New perspectives on semiring applications to dynamic
programming* (arXiv:2512.03916). Aeneas-extracted definitions land in `Extracted/` and
are related to this model by refinement theorems (see `FORMALISM.md`, layer 3).

STATUS: NOT YET CHECKED BY LEAN. Written without a Lean toolchain in the loop; expect
to fix names and tactics on first `lake build`. Every theorem is `sorry`.
-/
import Mathlib

namespace Formalism

abbrev Var := ℕ
abbrev Val := ℕ

/-- A finite functional relation: a partial assignment `Var ⇀ Val`. -/
def Functional (s : Finset (Var × Val)) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, p.1 = q.1 → p = q

abbrev Assign := { s : Finset (Var × Val) // Functional s }

namespace Assign

def dom (f : Assign) : Finset Var := f.1.image Prod.fst

def empty : Assign := ⟨∅, by simp [Functional]⟩

def single (s : Var) (t : Val) : Assign :=
  ⟨{(s, t)}, by simp [Functional]⟩

/-- Left-biased union; total, and equal to the plain union when domains are disjoint. -/
def join (f g : Assign) : Assign :=
  ⟨f.1 ∪ g.1.filter (fun q => q.1 ∉ f.dom), by sorry⟩

end Assign

/-- `E ::= ∅ | T^∅ | (s ↦ t) | E ⊎ E | E ⨝ E` (Definition 7). Mirrors `expr::Expr`. -/
inductive Expr
  | empty
  | unit
  | leaf (s : Var) (t : Val)
  | union (a b : Expr)
  | join (a b : Expr)

/-- `⟦E⟧` as a relation (Definition 8). No derivation means FAIL. -/
inductive Sem : Expr → Finset Assign → Prop
  | empty : Sem .empty ∅
  | unit : Sem .unit {Assign.empty}
  | leaf (s t) : Sem (.leaf s t) {Assign.single s t}
  | union {a b A B} :
      Sem a A → Sem b B → Disjoint A B →
      (∀ f ∈ A, ∀ g ∈ B, f.dom = g.dom) →
      Sem (.union a b) (A ∪ B)
  | join {a b A B} :
      Sem a A → Sem b B →
      (∀ f ∈ A, ∀ g ∈ B, Disjoint f.dom g.dom) →
      Sem (.join a b) ((A ×ˢ B).image fun p => p.1.join p.2)

section Measure
variable {A : Type*} [CommSemiring A]

/-- Definition 9: `μ(F) = Σ_{f ∈ F} Π_{s ∈ dom f} M[s, f s]`. -/
def measure (M : Var → Val → A) (F : Finset Assign) : A :=
  ∑ f ∈ F, ∏ p ∈ f.1, M p.1 p.2

/-- Mirrors `expr::eval`. -/
def eval (M : Var → Val → A) : Expr → A
  | .empty => 0
  | .unit => 1
  | .leaf s t => M s t
  | .union a b => eval M a + eval M b
  | .join a b => eval M a * eval M b

/-- Lemma 1: on legal expressions, linear-time evaluation equals the measure. -/
theorem eval_eq_measure (M : Var → Val → A) {e : Expr} {F : Finset Assign}
    (h : Sem e F) : eval M e = measure M F := by
  induction h with
  | empty => simp [eval, measure]
  | unit => sorry
  | leaf s t => sorry
  | union _ _ hdisj _ iha ihb => sorry
  | join _ _ hdom iha ihb => sorry

end Measure

/-! ## The Δ-product (Section 4) -/

/-- Totally ordered idempotent dioid with a regularity predicate. Mirrors `semiring::Dioid`. -/
class Dioid (D : Type*) extends CommSemiring D, LinearOrder D where
  add_eq_min : ∀ a b : D, a + b = min a b
  regular : D → Prop
  regular_cancel : ∀ a b c : D, regular a → a * b = a * c → b = c
  zero_not_regular : ¬ regular 0

/-- Definition 12: `D Δ A = {(d, a) | regular d ∨ a = 0}`. -/
structure Delta (D A : Type*) [Dioid D] [CommSemiring A] where
  d : D
  a : A
  inv : Dioid.regular d ∨ a = 0

/-- Theorem 3: `D Δ A` is a commutative semiring. -/
instance {D A : Type*} [Dioid D] [CommSemiring A] [DecidableEq D] : CommSemiring (Delta D A) := by
  sorry

/-! ## The generic trace DP (Remark 3) -/

/-- Mirrors `scheme::Node`. -/
inductive Node (Op : Type*)
  | mk (op : Op) (children : List (Node Op))

/-- Mirrors `scheme::Traced`: the executable part of an instance. -/
structure Traced (Op Tau : Type*) where
  step : Op → List Tau → List (Tau × List (Var × Val))
  accept : Tau → Bool

/-- The specification side of an instance: what the construction builds and what a trace is. -/
structure Instance (Op Tau : Type*) extends Traced Op Tau where
  /-- Partial candidates built at a node, each with the variables it owns. -/
  candidates : Node Op → Finset Assign
  /-- Trace of a partial candidate at a node. -/
  trace : Node Op → Assign → Tau
  /-- Obligation 2: solutionhood from the trace alone. -/
  solution : Node Op → Assign → Prop
  accept_iff : ∀ n f, f ∈ candidates n → (solution n f ↔ accept (trace n f) = true)
  /-- Obligation 3: `step` is the compositional image of `trace` (stated per instance). -/
  step_sound : True

/-- Mirrors `scheme::solve`. Defined on the Lean side so the theorem is about the model;
    the extracted `formalism.scheme.solve` refines it. -/
noncomputable def solve {Op Tau : Type*} [DecidableEq Tau] (I : Instance Op Tau) (n : Node Op) : Expr :=
  sorry

/-- Claim 1 at the root: the DP's output denotes exactly the solution set. -/
theorem solve_sound {Op Tau : Type*} [DecidableEq Tau] (I : Instance Op Tau) (n : Node Op) :
    Sem (solve I n) ((I.candidates n).filter fun f => I.accept (I.trace n f) = true) := by
  sorry

end Formalism
