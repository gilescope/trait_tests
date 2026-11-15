import Mathlib
/-!
# Specification of the formalism

Hand-written model of `explore/formalism/src/{expr,scheme,semiring}.rs`, after
Baril, Couceiro, Lagerkvist, *New perspectives on semiring applications to dynamic
programming* (arXiv:2512.03916). Aeneas-extracted definitions land in `Extracted/` and
are related to this model by refinement theorems (see `FORMALISM.md`, layer 3).

STATUS: NOT YET CHECKED BY LEAN. Written without a Lean toolchain in the loop; expect
to fix names and tactics on first `lake build`. Every theorem is `sorry`.
-/

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

theorem fst_mem_dom {f : Assign} {p : Var × Val} (hp : p ∈ f.1) : p.1 ∈ f.dom :=
  Finset.mem_image_of_mem Prod.fst hp

/-- Left-biased union; total, and equal to the plain union when domains are disjoint. -/
def join (f g : Assign) : Assign :=
  ⟨f.1 ∪ g.1.filter (fun q => q.1 ∉ f.dom), by
    intro p hp q hq hpq
    rw [Finset.mem_union, Finset.mem_filter] at hp hq
    rcases hp with hp | ⟨hp, hpd⟩ <;> rcases hq with hq | ⟨hq, hqd⟩
    · exact f.2 p hp q hq hpq
    · exact absurd (hpq ▸ fst_mem_dom hp) hqd
    · exact absurd (hpq ▸ fst_mem_dom hq) hpd
    · exact g.2 p hp q hq hpq⟩

/-- With disjoint domains the left-biased union is the plain union. -/
theorem join_val {f g : Assign} (h : Disjoint f.dom g.dom) : (f.join g).1 = f.1 ∪ g.1 := by
  show f.1 ∪ g.1.filter (fun q => q.1 ∉ f.dom) = f.1 ∪ g.1
  congr 1
  apply Finset.filter_true_of_mem
  intro q hq
  exact Finset.disjoint_right.mp h (fst_mem_dom hq)

theorem join_dom {f g : Assign} (h : Disjoint f.dom g.dom) :
    (f.join g).dom = f.dom ∪ g.dom := by
  unfold dom
  rw [join_val h, Finset.image_union]

/-- The pair sets of two assignments with disjoint domains are disjoint. -/
theorem disjoint_val {f g : Assign} (h : Disjoint f.dom g.dom) : Disjoint f.1 g.1 := by
  rw [Finset.disjoint_left]
  intro p hpf hpg
  exact Finset.disjoint_left.mp h (fst_mem_dom hpf) (fst_mem_dom hpg)

/-- Restriction to a set of variables. -/
def restrict (f : Assign) (D : Finset Var) : Assign :=
  ⟨f.1.filter (fun p => p.1 ∈ D), fun p hp q hq hpq =>
    f.2 p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq⟩

theorem restrict_dom_self (f : Assign) : f.restrict f.dom = f := by
  apply Subtype.ext
  show f.1.filter (fun p => p.1 ∈ f.dom) = f.1
  exact Finset.filter_true_of_mem fun p hp => fst_mem_dom hp

/-- A join is undone by restricting to either domain. -/
theorem join_restrict_left {f g : Assign} (h : Disjoint f.dom g.dom) :
    (f.join g).restrict f.dom = f := by
  apply Subtype.ext
  show (f.join g).1.filter (fun p => p.1 ∈ f.dom) = f.1
  rw [join_val h, Finset.filter_union]
  have hg : g.1.filter (fun p => p.1 ∈ f.dom) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p hp
    exact Finset.disjoint_right.mp h (fst_mem_dom hp)
  rw [hg, Finset.union_empty]
  exact Finset.filter_true_of_mem fun p hp => fst_mem_dom hp

theorem join_restrict_right {f g : Assign} (h : Disjoint f.dom g.dom) :
    (f.join g).restrict g.dom = g := by
  apply Subtype.ext
  show (f.join g).1.filter (fun p => p.1 ∈ g.dom) = g.1
  rw [join_val h, Finset.filter_union]
  have hf : f.1.filter (fun p => p.1 ∈ g.dom) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p hp
    exact Finset.disjoint_left.mp h (fst_mem_dom hp)
  rw [hf, Finset.empty_union]
  exact Finset.filter_true_of_mem fun p hp => fst_mem_dom hp

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

/-- All assignments denoted by a legal expression share one domain (`dom(E)` in the paper). -/
theorem Sem.dom_eq {e : Expr} {F : Finset Assign} (h : Sem e F) :
    ∀ f ∈ F, ∀ g ∈ F, f.dom = g.dom := by
  induction h with
  | empty => simp
  | unit =>
    intro f hf g hg
    rw [Finset.mem_singleton] at hf hg
    rw [hf, hg]
  | leaf s t =>
    intro f hf g hg
    rw [Finset.mem_singleton] at hf hg
    rw [hf, hg]
  | union _ _ _ hdomeq iha ihb =>
    intro f hf g hg
    rw [Finset.mem_union] at hf hg
    rcases hf with hf | hf <;> rcases hg with hg | hg
    · exact iha f hf g hg
    · exact hdomeq f hf g hg
    · exact (hdomeq g hg f hf).symm
    · exact ihb f hf g hg
  | join _ _ hdis iha ihb =>
    intro f hf g hg
    rw [Finset.mem_image] at hf hg
    obtain ⟨⟨f1, f2⟩, hp, rfl⟩ := hf
    obtain ⟨⟨g1, g2⟩, hq, rfl⟩ := hg
    rw [Finset.mem_product] at hp hq
    rw [Assign.join_dom (hdis _ hp.1 _ hp.2), Assign.join_dom (hdis _ hq.1 _ hq.2),
      iha _ hp.1 _ hq.1, ihb _ hp.2 _ hq.2]

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
  | unit => simp [eval, measure, Assign.empty]
  | leaf s t => simp [eval, measure, Assign.single]
  | union _ _ hdisj _ iha ihb =>
    -- a disjoint union is a sum of sums
    simp only [eval]
    rw [iha, ihb]
    unfold measure
    exact (Finset.sum_union hdisj).symm
  | @join a b SA SB ha hb hdom iha ihb =>
    -- the join of two sets with disjoint domains is a product of sums
    simp only [eval]
    rw [iha, ihb]
    unfold measure
    -- `(f, g) ↦ f.join g` is injective on `SA ×ˢ SB`: every `f ∈ SA` has the same domain, so
    -- restricting a join to that domain gives `f` back; likewise for `SB`
    have hinj : ∀ p ∈ SA ×ˢ SB, ∀ q ∈ SA ×ˢ SB,
        (fun p : Assign × Assign => p.1.join p.2) p =
          (fun p : Assign × Assign => p.1.join p.2) q → p = q := by
      intro p hp q hq hpq
      have hpq' : p.1.join p.2 = q.1.join q.2 := hpq
      rw [Finset.mem_product] at hp hq
      have hdA : p.1.dom = q.1.dom := Sem.dom_eq ha _ hp.1 _ hq.1
      have hdB : p.2.dom = q.2.dom := Sem.dom_eq hb _ hp.2 _ hq.2
      have h1 : p.1 = q.1 := by
        rw [← Assign.join_restrict_left (hdom _ hp.1 _ hp.2), hpq', hdA,
          Assign.join_restrict_left (hdom _ hq.1 _ hq.2)]
      have h2 : p.2 = q.2 := by
        rw [← Assign.join_restrict_right (hdom _ hp.1 _ hp.2), hpq', hdB,
          Assign.join_restrict_right (hdom _ hq.1 _ hq.2)]
      exact Prod.ext h1 h2
    rw [Finset.sum_image hinj, Finset.sum_product, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun f hf => Finset.sum_congr rfl fun g hg => ?_
    -- the product over `f.join g` splits, because the pair sets are disjoint
    show (∏ p ∈ f.1, M p.1 p.2) * ∏ p ∈ g.1, M p.1 p.2 = ∏ p ∈ (f.join g).1, M p.1 p.2
    rw [Assign.join_val (hdom f hf g hg), Finset.prod_union (Assign.disjoint_val (hdom f hf g hg))]

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
