import Mathlib
/-!
# Specification of the formalism

Hand-written model of `explore/formalism/src/{expr,scheme,semiring}.rs`, after
Baril, Couceiro, Lagerkvist, *New perspectives on semiring applications to dynamic
programming* (arXiv:2512.03916). Aeneas-extracted definitions land in `Extracted/` and
are related to this model by refinement theorems (see `FORMALISM.md`, layer 3).

Checked by `lake build` in CI (`+verify` in the Earthfile). Lemma 1 (`eval_eq_measure`) is
and Theorem 3 (`D Δ A` is a commutative semiring) are proved; the DP soundness claim is still `sorry`.
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

/-- Totally ordered idempotent dioid: `+` is `min` for the order. Mirrors `semiring::Dioid`. -/
class Dioid (D : Type*) extends CommSemiring D, LinearOrder D where
  add_eq_min : ∀ a b : D, a + b = min a b

namespace Dioid
variable {D : Type*} [Dioid D]

/-- Regular = cancellative. The Rust `Dioid::regular` must agree with this (a law, not a
    definition, on that side: it is what makes `Delta::new` a semiring). -/
def regular (d : D) : Prop := ∀ b c : D, d * b = d * c → b = c

theorem regular_one : regular (1 : D) := fun b c h => by simpa using h

theorem regular_mul {a b : D} (ha : regular a) (hb : regular b) : regular (a * b) :=
  fun x y h => hb x y (ha _ _ (by rwa [← mul_assoc, ← mul_assoc]))

/-- `0` is the greatest element: `a + 0 = a` and `+` is `min`. -/
theorem le_zero (d : D) : d ≤ 0 := by
  have h := Dioid.add_eq_min d 0
  rw [add_zero] at h
  exact min_eq_left_iff.mp h.symm

/-- Multiplication is monotone, by distributivity over `min`. -/
theorem mul_le_mul_left (a : D) {b c : D} (h : b ≤ c) : a * b ≤ a * c := by
  have hbc : b + c = b := by rw [Dioid.add_eq_min, min_eq_left h]
  have hm : a * b + a * c = a * b := by rw [← mul_add, hbc]
  rw [Dioid.add_eq_min] at hm
  exact min_eq_left_iff.mp hm

end Dioid

/-- Definition 12: `D Δ A = {(d, a) | regular d ∨ a = 0}`. -/
@[ext]
structure Delta (D A : Type*) [Dioid D] [CommSemiring A] where
  d : D
  a : A
  inv : Dioid.regular d ∨ a = 0

namespace Delta
variable {D A : Type*} [Dioid D] [CommSemiring A]

/-- The count carried by a sum: that of the strictly smaller cost, both on a tie. -/
def addA (d₁ : D) (a₁ : A) (d₂ : D) (a₂ : A) : A :=
  if d₁ < d₂ then a₁ else if d₂ < d₁ then a₂ else a₁ + a₂

@[simp] theorem addA_of_lt {d₁ d₂ : D} (h : d₁ < d₂) (a₁ a₂ : A) : addA d₁ a₁ d₂ a₂ = a₁ := by
  simp [addA, h]

@[simp] theorem addA_of_gt {d₁ d₂ : D} (h : d₂ < d₁) (a₁ a₂ : A) : addA d₁ a₁ d₂ a₂ = a₂ := by
  simp [addA, h, lt_asymm h]

@[simp] theorem addA_self (d : D) (a₁ a₂ : A) : addA d a₁ d a₂ = a₁ + a₂ := by
  simp [addA]

theorem addA_comm (d₁ d₂ : D) (a₁ a₂ : A) : addA d₁ a₁ d₂ a₂ = addA d₂ a₂ d₁ a₁ := by
  rcases lt_trichotomy d₁ d₂ with h | h | h <;> (try subst h) <;> simp [*, lt_asymm, add_comm]

set_option linter.unusedSimpArgs false in
theorem addA_assoc (d₁ d₂ d₃ : D) (a₁ a₂ a₃ : A) :
    addA (min d₁ d₂) (addA d₁ a₁ d₂ a₂) d₃ a₃ = addA d₁ a₁ (min d₂ d₃) (addA d₂ a₂ d₃ a₃) := by
  rcases lt_trichotomy d₁ d₂ with h1 | h1 | h1 <;>
  rcases lt_trichotomy d₂ d₃ with h2 | h2 | h2 <;>
  rcases lt_trichotomy d₁ d₃ with h3 | h3 | h3 <;>
  (try subst h1) <;> (try subst h2) <;> (try subst h3) <;>
  first
    | (exfalso; order)
    | simp [*, le_of_lt, lt_asymm, min_eq_left, min_eq_right, add_assoc]

/-- `add` keeps the `D`-minimum and the count of the argmin, summing counts on a tie. -/
def add (x y : Delta D A) : Delta D A where
  d := min x.d y.d
  a := addA x.d x.a y.d y.a
  inv := by
    rcases lt_trichotomy x.d y.d with h | h | h
    · rw [min_eq_left h.le, addA_of_lt h]; exact x.inv
    · rw [h, min_self, addA_self]
      rcases y.inv with hr | hz
      · exact Or.inl hr
      · rcases x.inv with hr' | hz'
        · exact Or.inl (h ▸ hr')
        · exact Or.inr (by rw [hz', hz, add_zero])
    · rw [min_eq_right h.le, addA_of_gt h]; exact y.inv

/-- `mul` is componentwise; the invariant survives because regular elements are closed under
    products and a non-regular factor carries count `0`. -/
def mul (x y : Delta D A) : Delta D A where
  d := x.d * y.d
  a := x.a * y.a
  inv := by
    by_cases hx : Dioid.regular x.d
    · by_cases hy : Dioid.regular y.d
      · exact Or.inl (Dioid.regular_mul hx hy)
      · exact Or.inr (by rw [y.inv.resolve_left hy, mul_zero])
    · exact Or.inr (by rw [x.inv.resolve_left hx, zero_mul])

instance : Zero (Delta D A) := ⟨⟨0, 0, Or.inr rfl⟩⟩
instance : One (Delta D A) := ⟨⟨1, 1, Or.inl Dioid.regular_one⟩⟩
instance : Add (Delta D A) := ⟨add⟩
instance : Mul (Delta D A) := ⟨mul⟩

@[simp] theorem add_d (x y : Delta D A) : (x + y).d = min x.d y.d := rfl
@[simp] theorem add_a (x y : Delta D A) : (x + y).a = addA x.d x.a y.d y.a := rfl
@[simp] theorem mul_d (x y : Delta D A) : (x * y).d = x.d * y.d := rfl
@[simp] theorem mul_a (x y : Delta D A) : (x * y).a = x.a * y.a := rfl
@[simp] theorem zero_d : (0 : Delta D A).d = 0 := rfl
@[simp] theorem zero_a : (0 : Delta D A).a = 0 := rfl
@[simp] theorem one_d : (1 : Delta D A).d = 1 := rfl
@[simp] theorem one_a : (1 : Delta D A).a = 1 := rfl

theorem mul_comm' (x y : Delta D A) : x * y = y * x := by
  ext <;> simp [mul_comm]

/-- Distributivity is where the invariant is needed: if `x.d` does not separate `y.d` from
    `z.d` then `x.d` is not regular, so `x.a = 0` and both sides vanish. -/
theorem left_distrib' (x y z : Delta D A) : x * (y + z) = x * y + x * z := by
  ext
  · rcases le_total y.d z.d with h | h
    · simp [min_eq_left h, min_eq_left (Dioid.mul_le_mul_left x.d h)]
    · simp [min_eq_right h, min_eq_right (Dioid.mul_le_mul_left x.d h)]
  · simp only [mul_a, add_a, mul_d]
    rcases lt_trichotomy y.d z.d with h | h | h
    · rcases (Dioid.mul_le_mul_left x.d h.le).lt_or_eq with h' | h'
      · simp [h, h']
      · have hx : x.a = 0 := by
          rcases x.inv with hr | hz
          · exact absurd (hr _ _ h') h.ne
          · exact hz
        simp [h, h', hx]
    · simp [h, mul_add]
    · rcases (Dioid.mul_le_mul_left x.d h.le).lt_or_eq with h' | h'
      · simp [h, h']
      · have hx : x.a = 0 := by
          rcases x.inv with hr | hz
          · exact absurd (hr _ _ h') h.ne
          · exact hz
        simp [h, h', hx]

/-- Theorem 3: `D Δ A` is a commutative semiring. -/
instance : CommSemiring (Delta D A) where
  add := (· + ·)
  add_assoc x y z := by
    ext
    · simp [min_assoc]
    · simp only [add_a, add_d]
      exact addA_assoc _ _ _ _ _ _
  zero := 0
  nsmul := nsmulRec
  zero_add x := by
    ext
    · simp [min_eq_right (Dioid.le_zero x.d)]
    · simp [addA, not_lt.mpr (Dioid.le_zero x.d)]
  add_zero x := by
    ext
    · simp [min_eq_left (Dioid.le_zero x.d)]
    · simp [addA, not_lt.mpr (Dioid.le_zero x.d)]
  add_comm x y := by
    ext
    · simp [min_comm]
    · simp only [add_a]
      exact addA_comm _ _ _ _
  mul := (· * ·)
  left_distrib := left_distrib'
  right_distrib x y z := by
    rw [mul_comm' (x + y) z, left_distrib', mul_comm' z x, mul_comm' z y]
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  mul_assoc x y z := by ext <;> simp [mul_assoc]
  one := 1
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  mul_comm := mul_comm'

end Delta

/-! ## The generic trace DP (Remark 3)

The executable model mirrors `scheme.rs` constructor for constructor, smart constructors
included, so that the refinement to the Aeneas extraction is syntactic. -/

/-- Mirrors `scheme::Node`. -/
inductive Node (Op : Type*)
  | mk (op : Op) (children : List (Node Op))

/-- Mirrors `scheme::Traced`: the executable part of an instance. -/
structure Traced (Op Tau : Type*) where
  step : Op → List Tau → List (Tau × List (Var × Val))
  accept : Tau → Bool

namespace Expr

/-- `expr::union`: `∅` is the unit. -/
def union' : Expr → Expr → Expr
  | .empty, b => b
  | a, .empty => a
  | a, b => .union a b

/-- `expr::join`: `T^∅` is the unit, `∅` the zero. -/
def join' : Expr → Expr → Expr
  | .empty, _ => .empty
  | _, .empty => .empty
  | .unit, b => b
  | a, .unit => a
  | a, b => .join a b

/-- `expr::join_leaves`: `E ⨝ (s₁ ↦ t₁) ⨝ … ⨝ (sₙ ↦ tₙ)`. -/
def joinLeaves (e : Expr) (leaves : List (Var × Val)) : Expr :=
  leaves.foldl (fun acc p => join' acc (.leaf p.1 p.2)) e

end Expr

namespace Traced
variable {Op Tau : Type*} [DecidableEq Tau]

/-- Mirrors `scheme::Table`: rows with distinct traces. -/
abbrev Table (Tau : Type*) := List (Tau × Expr)

/-- Mirrors `scheme::union_into`: `⊎` into the row of `tau`, or a new row. -/
def unionInto : Table Tau → Tau → Expr → Table Tau
  | [], tau, e => [(tau, e)]
  | (t, e') :: rows, tau, e =>
    if t = tau then (t, Expr.union' e' e) :: rows else (t, e') :: unionInto rows tau e

/-- Mirrors `scheme::step_node`: one row from each child, every way (`List.sections`); each
    `(trace, leaves)` the step yields joins the leaves onto the children's expressions and goes
    into the row of that trace. -/
def stepNode (I : Traced Op Tau) (op : Op) (tables : List (Table Tau)) : Table Tau :=
  tables.sections.foldl
    (fun table rows =>
      let joined := rows.foldl (fun acc r => Expr.join' acc r.2) Expr.unit
      (I.step op (rows.map Prod.fst)).foldl
        (fun table out => unionInto table out.1 (Expr.joinLeaves joined out.2)) table)
    []

mutual
/-- Mirrors `scheme::run`: post-order fold of `stepNode` over the construction. -/
def run (I : Traced Op Tau) : Node Op → Table Tau
  | .mk op cs => stepNode I op (runList I cs)
def runList (I : Traced Op Tau) : List (Node Op) → List (Table Tau)
  | [] => []
  | c :: cs => run I c :: runList I cs
end

/-- Mirrors `scheme::solve`: `⊎` of the accepted rows of the root table. -/
def solve (I : Traced Op Tau) (root : Node Op) : Expr :=
  (run I root).foldl (fun e row => if I.accept row.1 then Expr.union' e row.2 else e) .empty

end Traced

/-- The specification side of an instance: what the construction denotes and what a trace is.
    Obligation 2 of `Traced` is `accept_iff`. Obligation 3, that `step` is the compositional
    image of `trace` on the candidate sets, is the hypothesis Claim 1 needs; it is not yet
    stated here (see `solve_sound`). -/
structure Instance (Op Tau : Type*) extends Traced Op Tau where
  /-- Partial candidates built at a node, each with the variables it owns. -/
  candidates : Node Op → Finset Assign
  /-- Trace of a partial candidate at a node. -/
  trace : Node Op → Assign → Tau
  /-- Obligation 2: solutionhood from the trace alone. -/
  solution : Node Op → Assign → Prop
  accept_iff : ∀ n f, f ∈ candidates n → (solution n f ↔ accept (trace n f) = true)

/-- Claim 1 at the root: the DP's output denotes exactly the solution set. Not yet proved: the
    compositional obligation on `step` (the candidates at a node are the joins of one candidate
    per child with the leaves `step` yields for their traces, over disjoint variables) has to be
    stated as a hypothesis first. -/
theorem solve_sound {Op Tau : Type*} [DecidableEq Tau] (I : Instance Op Tau) (n : Node Op) :
    Sem (I.toTraced.solve n) ((I.candidates n).filter fun f => I.accept (I.trace n f) = true) := by
  sorry

end Formalism
