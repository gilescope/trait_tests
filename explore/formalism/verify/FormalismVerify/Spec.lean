import Mathlib
/-!
# Specification of the formalism

Hand-written model of `explore/formalism/src/{expr,scheme,semiring}.rs`, after
Baril, Couceiro, Lagerkvist, *New perspectives on semiring applications to dynamic
programming* (arXiv:2512.03916). Aeneas-extracted definitions land in `Extracted/` and
are related to this model by refinement theorems (see `FORMALISM.md`, layer 3).

Checked by `lake build` in CI (`+verify` in the Earthfile). Proved, with no `sorry`: Lemma 1
(`eval_eq_measure`), Theorem 3 (`D Δ A` is a commutative semiring) and Claim 1 (`solve_sound`:
on a well-formed construction the trace DP's output denotes exactly the solution set, given the
`Instance` obligations; `Bits.lean` discharges them for a concrete instance).
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

theorem empty_dom : (empty : Assign).dom = ∅ := by
  simp [dom, empty]

theorem single_dom (s : Var) (t : Val) : (single s t).dom = {s} := by
  simp [dom, single]

theorem empty_join (g : Assign) : empty.join g = g := by
  apply Subtype.ext
  show (∅ : Finset (Var × Val)) ∪ g.1.filter (fun q => q.1 ∉ empty.dom) = g.1
  simp [empty_dom]

theorem join_empty (f : Assign) : f.join empty = f := by
  apply Subtype.ext
  show f.1 ∪ (∅ : Finset (Var × Val)).filter (fun q => q.1 ∉ f.dom) = f.1
  simp

/-- Joins of pairwise disjoint assignments associate. -/
theorem join_assoc {f g h : Assign} (hfg : Disjoint f.dom g.dom) (hfh : Disjoint f.dom h.dom)
    (hgh : Disjoint g.dom h.dom) : (f.join g).join h = f.join (g.join h) := by
  apply Subtype.ext
  have hfg' : Disjoint (f.join g).dom h.dom := by
    rw [join_dom hfg]; exact Finset.disjoint_union_left.mpr ⟨hfh, hgh⟩
  have hgh' : Disjoint f.dom (g.join h).dom := by
    rw [join_dom hgh]; exact Finset.disjoint_union_right.mpr ⟨hfg, hfh⟩
  rw [join_val hfg', join_val hfg, join_val hgh', join_val hgh, Finset.union_assoc]

/-- The join of a list of assignments, left to right from `empty`. -/
def joinAll (fs : List Assign) : Assign := fs.foldl join empty

/-- The assignment a list of leaves denotes (`join_leaves` on the assignment side). -/
def ofList : List (Var × Val) → Assign
  | [] => empty
  | p :: rest => (single p.1 p.2).join (ofList rest)

theorem ofList_dom :
    ∀ l : List (Var × Val), (l.map Prod.fst).Nodup → (ofList l).dom = (l.map Prod.fst).toFinset
  | [], _ => by simp [ofList, empty_dom]
  | p :: rest, hl => by
    rw [List.map_cons, List.nodup_cons] at hl
    have ih := ofList_dom rest hl.2
    have hd : Disjoint (single p.1 p.2).dom (ofList rest).dom := by
      rw [single_dom, ih, Finset.disjoint_singleton_left, List.mem_toFinset]
      exact hl.1
    rw [ofList, join_dom hd, single_dom, ih, List.map_cons, List.toFinset_cons, Finset.insert_eq]

theorem join_dom_subset (f g : Assign) : (f.join g).dom ⊆ f.dom ∪ g.dom := by
  intro x hx
  rw [dom, Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have hp' : p ∈ f.1 ∪ g.1.filter (fun q => q.1 ∉ f.dom) := hp
  rw [Finset.mem_union, Finset.mem_filter] at hp'
  rcases hp' with h | ⟨h, _⟩
  · exact Finset.mem_union_left _ (fst_mem_dom h)
  · exact Finset.mem_union_right _ (fst_mem_dom h)

/-- Restricting away from `g`'s variables ignores `g`. -/
theorem restrict_join_of_disjoint_right {f g : Assign} {D : Finset Var} (h : Disjoint D g.dom) :
    (f.join g).restrict D = f.restrict D := by
  apply Subtype.ext
  show (f.1 ∪ g.1.filter (fun q => q.1 ∉ f.dom)).filter (fun p => p.1 ∈ D) =
    f.1.filter (fun p => p.1 ∈ D)
  rw [Finset.filter_union]
  have hg : (g.1.filter (fun q => q.1 ∉ f.dom)).filter (fun p => p.1 ∈ D) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p hp hpD
    rw [Finset.mem_filter] at hp
    exact Finset.disjoint_left.mp h hpD (fst_mem_dom hp.1)
  rw [hg, Finset.union_empty]

/-- Restricting away from `f`'s variables ignores `f`. -/
theorem restrict_join_of_disjoint_left {f g : Assign} {D : Finset Var} (h : Disjoint D f.dom) :
    (f.join g).restrict D = g.restrict D := by
  apply Subtype.ext
  show (f.1 ∪ g.1.filter (fun q => q.1 ∉ f.dom)).filter (fun p => p.1 ∈ D) =
    g.1.filter (fun p => p.1 ∈ D)
  rw [Finset.filter_union, Finset.filter_filter]
  have hf : f.1.filter (fun p => p.1 ∈ D) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p hp hpD
    exact Finset.disjoint_left.mp h hpD (fst_mem_dom hp)
  rw [hf, Finset.empty_union]
  apply Finset.filter_congr
  intro p _
  constructor
  · exact fun hh => hh.2
  · intro hpD
    exact ⟨fun hfd => Finset.disjoint_left.mp h hpD hfd, hpD⟩

theorem restrict_foldl_join {D : Finset Var} :
    ∀ (fs : List Assign) (e : Assign), (∀ g ∈ fs, Disjoint D g.dom) →
      (fs.foldl join e).restrict D = e.restrict D
  | [], _, _ => rfl
  | g :: fs, e, h => by
    rw [List.foldl_cons, restrict_foldl_join fs _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    exact restrict_join_of_disjoint_right (h g (List.mem_cons_self ..))

theorem dom_foldl_join_subset :
    ∀ (fs : List Assign) (e : Assign), (fs.foldl join e).dom ⊆ e.dom ∪ (fs.map dom).foldr (· ∪ ·) ∅
  | [], e => by simp
  | g :: fs, e => by
    rw [List.foldl_cons, List.map_cons, List.foldr_cons]
    intro x hx
    have hx' := dom_foldl_join_subset fs (e.join g) hx
    rw [Finset.mem_union] at hx' ⊢
    rcases hx' with h | h
    · rcases Finset.mem_union.mp (join_dom_subset e g h) with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_union_left _ h)
    · exact Or.inr (Finset.mem_union_right _ h)

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
  rcases lt_trichotomy d₁ d₂ with h | h | h <;> (try subst h) <;> simp [*, add_comm]

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

/-! Denotations of the smart constructors: the same sets as the raw constructors, so the
executable model and the relation `Sem` agree. -/

theorem image_join_singleton_left (B : Finset Assign) :
    (({Assign.empty} : Finset Assign) ×ˢ B).image (fun p : Assign × Assign => p.1.join p.2) = B := by
  ext g
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_singleton, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨rfl, hb⟩, rfl⟩
    rw [Assign.empty_join]; exact hb
  · intro hg
    exact ⟨Assign.empty, g, ⟨rfl, hg⟩, Assign.empty_join g⟩

theorem image_join_singleton_right (A : Finset Assign) :
    (A ×ˢ ({Assign.empty} : Finset Assign)).image (fun p : Assign × Assign => p.1.join p.2) = A := by
  ext f
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_singleton, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, rfl⟩, rfl⟩
    rw [Assign.join_empty]; exact ha
  · intro hf
    exact ⟨f, Assign.empty, ⟨hf, rfl⟩, Assign.join_empty f⟩

theorem image_join_product_singleton (A : Finset Assign) (g : Assign) :
    (A ×ˢ ({g} : Finset Assign)).image (fun p : Assign × Assign => p.1.join p.2) =
      A.image fun f => f.join g := by
  ext h
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_singleton, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, g, ⟨ha, rfl⟩, rfl⟩

theorem Sem.union' {a b : Expr} {A B : Finset Assign} (ha : Sem a A) (hb : Sem b B)
    (hdisj : Disjoint A B) (hdom : ∀ f ∈ A, ∀ g ∈ B, f.dom = g.dom) :
    Sem (Expr.union' a b) (A ∪ B) := by
  cases a <;> cases b <;> simp only [Expr.union'] <;> first
    | (cases ha; simpa using hb)
    | (cases hb; simpa using ha)
    | exact Sem.union ha hb hdisj hdom

theorem Sem.join' {a b : Expr} {A B : Finset Assign} (ha : Sem a A) (hb : Sem b B)
    (hdom : ∀ f ∈ A, ∀ g ∈ B, Disjoint f.dom g.dom) :
    Sem (Expr.join' a b) ((A ×ˢ B).image fun p => p.1.join p.2) := by
  cases a <;> cases b <;> simp only [Expr.join'] <;> first
    | (cases ha; simpa using Sem.empty)
    | (cases hb; simpa using Sem.empty)
    | (cases ha; rw [image_join_singleton_left]; exact hb)
    | (cases hb; rw [image_join_singleton_right]; exact ha)
    | exact Sem.join ha hb hdom

/-- `join_leaves` denotes the join with the leaves' assignment, when the leaves are variables
    new to the denoted assignments and distinct from each other. -/
theorem Sem.joinLeaves {e : Expr} {E : Finset Assign} (he : Sem e E) :
    ∀ l : List (Var × Val), (l.map Prod.fst).Nodup → (∀ f ∈ E, ∀ q ∈ l, q.1 ∉ f.dom) →
      Sem (Expr.joinLeaves e l) (E.image fun f => f.join (Assign.ofList l))
  | [], _, _ => by simpa [Expr.joinLeaves, Assign.ofList, Assign.join_empty] using he
  | p :: rest, hl, hnew => by
    rw [List.map_cons, List.nodup_cons] at hl
    -- one leaf in, then the rest
    have hstep : Sem (Expr.join' e (.leaf p.1 p.2)) (E.image fun f => f.join (Assign.single p.1 p.2)) := by
      rw [← image_join_product_singleton]
      apply Sem.join' he (Sem.leaf p.1 p.2)
      intro f hf g hg
      rw [Finset.mem_singleton] at hg
      rw [hg, Assign.single_dom, Finset.disjoint_singleton_right]
      exact hnew f hf p (List.mem_cons_self ..)
    have hnew' : ∀ f ∈ E.image (fun f => f.join (Assign.single p.1 p.2)), ∀ q ∈ rest, q.1 ∉ f.dom := by
      intro f hf q hq
      rw [Finset.mem_image] at hf
      obtain ⟨f0, hf0, rfl⟩ := hf
      have hd : Disjoint f0.dom (Assign.single p.1 p.2).dom := by
        rw [Assign.single_dom, Finset.disjoint_singleton_right]
        exact hnew f0 hf0 p (List.mem_cons_self ..)
      rw [Assign.join_dom hd, Assign.single_dom, Finset.mem_union, Finset.mem_singleton]
      rintro (h | h)
      · exact hnew f0 hf0 q (List.mem_cons_of_mem _ hq) h
      · exact hl.1 (h ▸ List.mem_map_of_mem hq)
    have ih := Sem.joinLeaves hstep rest hl.2 hnew'
    show Sem (Expr.joinLeaves (Expr.join' e (.leaf p.1 p.2)) rest) _
    convert ih using 1
    rw [Finset.image_image]
    apply Finset.image_congr
    intro f hf
    have hf : f ∈ E := Finset.mem_coe.mp hf
    show f.join ((Assign.single p.1 p.2).join (Assign.ofList rest)) =
      (f.join (Assign.single p.1 p.2)).join (Assign.ofList rest)
    have h1 : Disjoint f.dom (Assign.single p.1 p.2).dom := by
      rw [Assign.single_dom, Finset.disjoint_singleton_right]
      exact hnew f hf p (List.mem_cons_self ..)
    have h2 : Disjoint f.dom (Assign.ofList rest).dom := by
      rw [Assign.ofList_dom rest hl.2, Finset.disjoint_left]
      intro x hx hx'
      rw [List.mem_toFinset, List.mem_map] at hx'
      obtain ⟨q, hq, rfl⟩ := hx'
      exact hnew f hf q (List.mem_cons_of_mem _ hq) hx
    have h3 : Disjoint (Assign.single p.1 p.2).dom (Assign.ofList rest).dom := by
      rw [Assign.single_dom, Assign.ofList_dom rest hl.2, Finset.disjoint_singleton_left,
        List.mem_toFinset]
      exact hl.1
    exact (Assign.join_assoc h1 h2 h3).symm

/-- `Sem` is a partial function: an expression denotes at most one set. -/
theorem Sem.unique {e : Expr} {A B : Finset Assign} (ha : Sem e A) (hb : Sem e B) : A = B := by
  induction ha generalizing B with
  | empty => cases hb; rfl
  | unit => cases hb; rfl
  | leaf s t => cases hb; rfl
  | union _ _ _ _ iha ihb =>
    cases hb with
    | union ha' hb' _ _ => rw [iha ha', ihb hb']
  | join _ _ _ iha ihb =>
    cases hb with
    | join ha' hb' _ => rw [iha ha', ihb hb']

open Classical in
/-- The set an expression denotes (`∅` for an illegal expression). -/
noncomputable def denot (e : Expr) : Finset Assign := if h : ∃ A, Sem e A then h.choose else ∅

theorem Sem.denot_eq {e : Expr} {A : Finset Assign} (h : Sem e A) : denot e = A := by
  unfold denot
  rw [dite_eq_left (⟨A, h⟩ : ∃ A, Sem e A)]
  exact Sem.unique (Exists.choose_spec (⟨A, h⟩ : ∃ A, Sem e A)) h

theorem Sem.ne_empty {e : Expr} {A : Finset Assign} (h : Sem e A) (hA : A.Nonempty) : e ≠ .empty := by
  rintro rfl
  cases h
  exact Finset.not_nonempty_empty hA

namespace Traced
variable {Op Tau : Type*} [DecidableEq Tau]

/-- Mirrors `scheme::Table`: rows with distinct traces. -/
abbrev Table (Tau : Type*) := List (Tau × Expr)

/-- Mirrors `scheme::union_into`: `⊎` into the row of `tau`, or a new row. -/
def unionInto : Table Tau → Tau → Expr → Table Tau
  | [], tau, e => [(tau, e)]
  | (t, e') :: rows, tau, e =>
    if t = tau then (t, Expr.union' e' e) :: rows else (t, e') :: unionInto rows tau e

/-- The join of one row from each child (`joined` in `step_node`). -/
def joined (rows : List (Tau × Expr)) : Expr :=
  rows.foldl (fun acc r => Expr.join' acc r.2) Expr.unit

/-- What one tuple of child rows contributes: a `(trace, expression)` per `step` output. -/
def rowItems (I : Traced Op Tau) (op : Op) (rows : List (Tau × Expr)) : List (Tau × Expr) :=
  (I.step op (rows.map Prod.fst)).map fun out => (out.1, Expr.joinLeaves (joined rows) out.2)

/-- One element from each list, every way, in the order `scheme::step_node` visits them: the
    first child varies slowest and the last fastest (its odometer carries from the end). -/
def tuples {α : Type*} : List (List α) → List (List α)
  | [] => [[]]
  | l :: L => l.flatMap fun a => (tuples L).map (a :: ·)

theorem mem_tuples {α : Type*} : ∀ {L : List (List α)} {s : List α},
    s ∈ tuples L ↔ List.Forall₂ (· ∈ ·) s L
  | [], s => by
    simp only [tuples, List.mem_singleton]
    constructor
    · rintro rfl
      exact List.Forall₂.nil
    · intro h
      cases h
      rfl
  | l :: L, s => by
    simp only [tuples, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a, ha, t, ht, rfl⟩
      exact List.Forall₂.cons ha (mem_tuples.mp ht)
    · intro h
      cases h with
      | cons ha ht => exact ⟨_, ha, _, mem_tuples.mpr ht, rfl⟩

theorem nodup_tuples {α : Type*} :
    ∀ L : List (List α), (∀ l ∈ L, l.Nodup) → (tuples L).Nodup
  | [], _ => by simp [tuples]
  | l :: L, h => by
    rw [tuples, List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · intro a _
      exact (nodup_tuples L fun l' hl' => h l' (List.mem_cons_of_mem _ hl')).map
        fun s s' hss' => (List.cons.inj hss').2
    · refine List.Pairwise.imp ?_ (h l (List.mem_cons_self ..))
      intro a a' hne
      show List.Disjoint _ _
      rw [List.disjoint_left]
      intro x hx hx'
      rw [List.mem_map] at hx hx'
      obtain ⟨s, _, rfl⟩ := hx
      obtain ⟨s', _, hs'⟩ := hx'
      exact hne (List.cons.inj hs').1

/-- Mirrors `scheme::step_node`: one row from each child, every way (`tuples`, in the Rust's
    order); each `(trace, leaves)` the step yields joins the leaves onto the children's
    expressions and goes into the row of that trace. -/
def stepNode (I : Traced Op Tau) (op : Op) (tables : List (Table Tau)) : Table Tau :=
  (tuples tables).foldl
    (fun table rows => (rowItems I op rows).foldl (fun table it => unionInto table it.1 it.2) table)
    []

/-! ### Table semantics -/

/-- The expression of the row of `tau`; `∅` when there is none. -/
def rowExpr : Table Tau → Tau → Expr
  | [], _ => .empty
  | (t, e) :: rows, tau => if t = tau then e else rowExpr rows tau

/-- Row `tau` denotes `S tau` (so `S tau = ∅` where there is no row). -/
def TableSem (T : Table Tau) (S : Tau → Finset Assign) : Prop :=
  ∀ tau, Sem (rowExpr T tau) (S tau)

theorem rowExpr_unionInto (tau : Tau) (e : Expr) (τ : Tau) :
    ∀ T : Table Tau,
      rowExpr (unionInto T tau e) τ = if τ = tau then Expr.union' (rowExpr T tau) e else rowExpr T τ
  | [] => by
    simp only [unionInto, rowExpr]
    by_cases h : τ = tau
    · subst h; simp [Expr.union']
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
  | (t, e') :: rows => by
    by_cases ht : t = tau
    · subst ht
      by_cases h : τ = t
      · subst h; simp [unionInto, rowExpr]
      · simp [unionInto, rowExpr, h, Ne.symm h]
    · by_cases h : t = τ
      · subst h; simp [unionInto, rowExpr, ht]
      · simp [unionInto, rowExpr, ht, h, rowExpr_unionInto tau e τ rows]

/-- `union_into` adds a disjoint, same-domain set to the row of `tau`. -/
theorem TableSem.unionInto_sem {T : Table Tau} {S : Tau → Finset Assign} (hT : TableSem T S)
    {tau : Tau} {e : Expr} {E : Finset Assign} (he : Sem e E) (hdisj : Disjoint (S tau) E)
    (hdom : ∀ f ∈ S tau, ∀ g ∈ E, f.dom = g.dom) :
    TableSem (unionInto T tau e) fun τ => if τ = tau then S tau ∪ E else S τ := by
  intro τ
  dsimp only
  rw [rowExpr_unionInto]
  by_cases h : τ = tau
  · rw [ite_eq_left h, ite_eq_left h]
    exact Sem.union' (hT tau) he hdisj hdom
  · rw [ite_eq_right h, ite_eq_right h]
    exact hT τ

/-- The sets a list of items adds to row `τ`. -/
def itemsSet (D : Tau × Expr → Finset Assign) (items : List (Tau × Expr)) (τ : Tau) :
    Finset Assign :=
  (items.filter fun it => it.1 = τ).foldr (fun it acc => D it ∪ acc) ∅

/-- Folding `union_into` over items with pairwise disjoint denotations, all of one domain `Dn`,
    disjoint from what the table already holds. -/
theorem TableSem.foldl_unionInto {Dn : Finset Var} (D : Tau × Expr → Finset Assign) :
    ∀ (items : List (Tau × Expr)) {T : Table Tau} {S : Tau → Finset Assign}, TableSem T S →
      (∀ it ∈ items, Sem it.2 (D it)) →
      items.Pairwise (fun a b => Disjoint (D a) (D b)) →
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
    have hT' := TableSem.unionInto_sem hT (hD it (List.mem_cons_self ..)) (hS it (List.mem_cons_self ..))
      (fun f hf g hg => by rw [hdomS _ f hf, hdomD it (List.mem_cons_self ..) g hg])
    have ih := TableSem.foldl_unionInto (Dn := Dn) D items hT'
      (fun it' h => hD it' (List.mem_cons_of_mem _ h)) hpair.2
      (fun it' h => by
        by_cases heq : it'.1 = it.1
        · simp only [heq, ite_true]
          exact Finset.disjoint_union_left.mpr
            ⟨heq ▸ hS it' (List.mem_cons_of_mem _ h), hpair.1 it' h⟩
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

theorem foldl_unionInto_flatMap {α : Type*} (g : α → List (Tau × Expr)) :
    ∀ (L : List α) (T : Table Tau),
      L.foldl (fun T x => (g x).foldl (fun T it => unionInto T it.1 it.2) T) T =
        (L.flatMap g).foldl (fun T it => unionInto T it.1 it.2) T
  | [], _ => rfl
  | x :: L, T => by
    rw [List.foldl_cons, List.flatMap_cons, List.foldl_append]
    exact foldl_unionInto_flatMap g L _

theorem itemsSet_cons (D : Tau × Expr → Finset Assign) (it : Tau × Expr) (items : List (Tau × Expr))
    (τ : Tau) :
    itemsSet D (it :: items) τ = if it.1 = τ then D it ∪ itemsSet D items τ else itemsSet D items τ := by
  unfold itemsSet
  rw [List.filter_cons]
  by_cases h : it.1 = τ
  · simp [h]
  · simp [h]

theorem mem_itemsSet (D : Tau × Expr → Finset Assign) :
    ∀ (items : List (Tau × Expr)) (τ : Tau) (f : Assign),
      f ∈ itemsSet D items τ ↔ ∃ it ∈ items, it.1 = τ ∧ f ∈ D it
  | [], τ, f => by simp [itemsSet]
  | it :: items, τ, f => by
    rw [itemsSet_cons]
    by_cases h : it.1 = τ
    · rw [ite_eq_left h, Finset.mem_union, mem_itemsSet D items]
      constructor
      · rintro (hf | ⟨it', hit', hτ, hf⟩)
        · exact ⟨it, List.mem_cons_self .., h, hf⟩
        · exact ⟨it', List.mem_cons_of_mem _ hit', hτ, hf⟩
      · rintro ⟨it', hit', hτ, hf⟩
        rw [List.mem_cons] at hit'
        rcases hit' with rfl | hit'
        · exact Or.inl hf
        · exact Or.inr ⟨it', hit', hτ, hf⟩
    · rw [ite_eq_right h, mem_itemsSet D items]
      constructor
      · rintro ⟨it', hit', hτ, hf⟩
        exact ⟨it', List.mem_cons_of_mem _ hit', hτ, hf⟩
      · rintro ⟨it', hit', hτ, hf⟩
        rw [List.mem_cons] at hit'
        rcases hit' with rfl | hit'
        · exact absurd hτ h
        · exact ⟨it', hit', hτ, hf⟩

/-- `step_node` as one flat fold over every `(tuple of rows, step output)` item. -/
theorem stepNode_eq_foldl (I : Traced Op Tau) (op : Op) (tables : List (Table Tau)) :
    stepNode I op tables =
      ((tuples tables).flatMap (rowItems I op)).foldl (fun T it => unionInto T it.1 it.2) [] :=
  foldl_unionInto_flatMap (rowItems I op) (tuples tables) []

/-! ### The join of one row from each child -/

/-- The denotation of `joined`: joins of one assignment from each set. -/
def joinedSet (R : List (Finset Assign)) : Finset Assign :=
  R.foldl (fun acc A => (acc ×ˢ A).image fun p => p.1.join p.2) {Assign.empty}

theorem mem_foldl_join_image :
    ∀ (R : List (Finset Assign)) (E : Finset Assign) (f : Assign),
      f ∈ R.foldl (fun acc A => (acc ×ˢ A).image fun p => p.1.join p.2) E ↔
        ∃ e ∈ E, ∃ fs, List.Forall₂ (· ∈ ·) fs R ∧ f = fs.foldl Assign.join e
  | [], E, f => by
    constructor
    · intro hf
      exact ⟨f, hf, [], List.Forall₂.nil, rfl⟩
    · rintro ⟨e, he, fs, hfs, rfl⟩
      cases hfs
      exact he
  | A :: R, E, f => by
    rw [List.foldl_cons, mem_foldl_join_image R]
    constructor
    · rintro ⟨e', he', fs, hfs, rfl⟩
      rw [Finset.mem_image] at he'
      obtain ⟨⟨e, a⟩, hea, rfl⟩ := he'
      rw [Finset.mem_product] at hea
      exact ⟨e, hea.1, a :: fs, List.Forall₂.cons hea.2 hfs, rfl⟩
    · rintro ⟨e, he, fs, hfs, rfl⟩
      cases hfs with
      | cons ha hfs =>
        rename_i a fs'
        exact ⟨e.join a, Finset.mem_image.mpr ⟨(e, a), Finset.mem_product.mpr ⟨he, ha⟩, rfl⟩, fs', hfs,
          rfl⟩

theorem mem_joinedSet (R : List (Finset Assign)) (f : Assign) :
    f ∈ joinedSet R ↔ ∃ fs, List.Forall₂ (· ∈ ·) fs R ∧ f = Assign.joinAll fs := by
  unfold joinedSet
  rw [mem_foldl_join_image]
  constructor
  · rintro ⟨e, he, fs, hfs, rfl⟩
    rw [Finset.mem_singleton] at he
    exact ⟨fs, hfs, by rw [he]; rfl⟩
  · rintro ⟨fs, hfs, rfl⟩
    exact ⟨Assign.empty, Finset.mem_singleton_self _, fs, hfs, rfl⟩

omit [DecidableEq Tau] in
theorem Sem.joined_aux :
    ∀ (rows : List (Tau × Expr)) (R : List (Finset Assign)) (e : Expr) (E : Finset Assign),
      Sem e E → List.Forall₂ (fun r A => Sem r.2 A) rows R →
      (∀ A ∈ R, ∀ f ∈ E, ∀ g ∈ A, Disjoint f.dom g.dom) →
      R.Pairwise (fun A B => ∀ f ∈ A, ∀ g ∈ B, Disjoint f.dom g.dom) →
      Sem (rows.foldl (fun acc r => Expr.join' acc r.2) e)
        (R.foldl (fun acc A => (acc ×ˢ A).image fun p => p.1.join p.2) E)
  | [], [], _, _, he, _, _, _ => he
  | [], _ :: _, _, _, _, hF, _, _ => nomatch hF
  | _ :: _, [], _, _, _, hF, _, _ => nomatch hF
  | r :: rows, A :: R, e, E, he, hF, hdisj, hpair => by
    rw [List.forall₂_cons] at hF
    rw [List.pairwise_cons] at hpair
    simp only [List.foldl_cons]
    apply Sem.joined_aux rows R _ _ (Sem.join' he hF.1 (hdisj A (List.mem_cons_self ..))) hF.2
    · intro B hB h hh g' hg'
      rw [Finset.mem_image] at hh
      obtain ⟨⟨f, g⟩, hfg, rfl⟩ := hh
      rw [Finset.mem_product] at hfg
      rw [Assign.join_dom (hdisj A (List.mem_cons_self ..) f hfg.1 g hfg.2)]
      exact Finset.disjoint_union_left.mpr
        ⟨hdisj B (List.mem_cons_of_mem _ hB) f hfg.1 g' hg', hpair.1 B hB g hfg.2 g' hg'⟩
    · exact hpair.2

omit [DecidableEq Tau] in
/-- `joined` denotes the joins of one assignment per child, when the children's domains are
    pairwise disjoint. -/
theorem Sem.joined (rows : List (Tau × Expr)) (R : List (Finset Assign))
    (hF : List.Forall₂ (fun r A => Sem r.2 A) rows R)
    (hpair : R.Pairwise (fun A B => ∀ f ∈ A, ∀ g ∈ B, Disjoint f.dom g.dom)) :
    Sem (joined rows) (joinedSet R) := by
  apply Sem.joined_aux rows R Expr.unit {Assign.empty} Sem.unit hF _ hpair
  intro A _ f hf g _
  rw [Finset.mem_singleton] at hf
  rw [hf, Assign.empty_dom]
  exact Finset.disjoint_empty_left _

/-! ### Rows: lookup and distinct traces -/

theorem rowExpr_of_mem :
    ∀ {T : Table Tau}, (T.map Prod.fst).Nodup → ∀ {t : Tau} {e : Expr}, (t, e) ∈ T → rowExpr T t = e
  | [], _, _, _, h => nomatch h
  | (t', e') :: rows, hnd, t, e, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.mem_cons] at h
    rcases h with h | h
    · cases h
      simp [rowExpr]
    · have hne : t' ≠ t := by
        rintro rfl
        exact hnd.1 (List.mem_map.mpr ⟨(t', e), h, rfl⟩)
      rw [rowExpr, ite_eq_right hne]
      exact rowExpr_of_mem hnd.2 h

theorem eq_of_mem_of_fst_eq {T : Table Tau} (hnd : (T.map Prod.fst).Nodup) {r r' : Tau × Expr}
    (hr : r ∈ T) (hr' : r' ∈ T) (h : r.1 = r'.1) : r = r' := by
  have h1 := rowExpr_of_mem hnd (show (r.1, r.2) ∈ T from hr)
  have h2 := rowExpr_of_mem hnd (show (r'.1, r'.2) ∈ T from hr')
  rw [h] at h1
  exact Prod.ext h (h1.symm.trans h2)

theorem mem_of_rowExpr_ne :
    ∀ {T : Table Tau} {t : Tau}, rowExpr T t ≠ .empty → (t, rowExpr T t) ∈ T
  | [], _, h => absurd rfl h
  | (t', e') :: rows, t, h => by
    by_cases ht : t' = t
    · subst ht
      simp [rowExpr]
    · rw [rowExpr, ite_eq_right ht] at h ⊢
      exact List.mem_cons_of_mem _ (mem_of_rowExpr_ne h)

theorem mem_map_fst_unionInto :
    ∀ (T : Table Tau) (tau : Tau) (e : Expr) {x : Tau},
      x ∈ (unionInto T tau e).map Prod.fst → x ∈ T.map Prod.fst ∨ x = tau
  | [], tau, e, x, h => by
    simp [unionInto] at h
    exact Or.inr h
  | (t, e') :: rows, tau, e, x, h => by
    by_cases ht : t = tau
    · rw [unionInto, ite_eq_left ht] at h
      simp only [List.map_cons] at h ⊢
      exact Or.inl h
    · rw [unionInto, ite_eq_right ht, List.map_cons, List.mem_cons] at h
      rw [List.map_cons, List.mem_cons]
      rcases h with h | h
      · exact Or.inl (Or.inl h)
      · rcases mem_map_fst_unionInto rows tau e h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem nodup_unionInto :
    ∀ (T : Table Tau) (tau : Tau) (e : Expr),
      (T.map Prod.fst).Nodup → ((unionInto T tau e).map Prod.fst).Nodup
  | [], tau, e, _ => by simp [unionInto]
  | (t, e') :: rows, tau, e, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases ht : t = tau
    · rw [unionInto, ite_eq_left ht, List.map_cons, List.nodup_cons]
      exact hnd
    · rw [unionInto, ite_eq_right ht, List.map_cons, List.nodup_cons]
      refine ⟨?_, nodup_unionInto rows tau e hnd.2⟩
      intro hmem
      rcases mem_map_fst_unionInto rows tau e hmem with h | h
      · exact hnd.1 h
      · exact ht h

theorem nodup_foldl_unionInto :
    ∀ (items : List (Tau × Expr)) (T : Table Tau), (T.map Prod.fst).Nodup →
      ((items.foldl (fun T it => unionInto T it.1 it.2) T).map Prod.fst).Nodup
  | [], _, h => h
  | it :: items, T, h => nodup_foldl_unionInto items _ (nodup_unionInto T it.1 it.2 h)

theorem stepNode_nodup (I : Traced Op Tau) (op : Op) (tables : List (Table Tau)) :
    ((stepNode I op tables).map Prod.fst).Nodup := by
  rw [stepNode_eq_foldl]
  exact nodup_foldl_unionInto _ [] List.nodup_nil

mutual
/-- Mirrors `scheme::run`: post-order fold of `stepNode` over the construction. -/
def run (I : Traced Op Tau) : Node Op → Table Tau
  | .mk op cs => stepNode I op (runList I cs)
def runList (I : Traced Op Tau) : List (Node Op) → List (Table Tau)
  | [] => []
  | c :: cs => run I c :: runList I cs
end

theorem run_nodup (I : Traced Op Tau) (n : Node Op) : ((run I n).map Prod.fst).Nodup := by
  cases n with
  | mk op cs =>
    rw [run]
    exact stepNode_nodup I op (runList I cs)

/-- Mirrors `scheme::solve`: `⊎` of the accepted rows of the root table. -/
def solve (I : Traced Op Tau) (root : Node Op) : Expr :=
  (run I root).foldl (fun e row => if I.accept row.1 then Expr.union' e row.2 else e) .empty

end Traced

/-! ### List lemmas for the induction -/

theorem mem_zipWith_right {α β γ : Type*} (g : α → β → γ) :
    ∀ (as : List α) (bs : List β) {c : γ}, c ∈ List.zipWith g as bs → ∃ a b, b ∈ bs ∧ c = g a b
  | [], _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | a :: as, b :: bs, c, h => by
    rw [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨a, b, List.mem_cons_self .., h⟩
    · obtain ⟨a', b', hb', rfl⟩ := mem_zipWith_right g as bs h
      exact ⟨a', b', List.mem_cons_of_mem _ hb', rfl⟩

theorem pairwise_zipWith_right {α β γ : Type*} {P : β → β → Prop} {Q : γ → γ → Prop}
    (g : α → β → γ) (hg : ∀ a a' b b', P b b' → Q (g a b) (g a' b')) :
    ∀ (as : List α) (bs : List β), bs.Pairwise P → (List.zipWith g as bs).Pairwise Q
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: as, b :: bs, h => by
    rw [List.pairwise_cons] at h
    rw [List.zipWith_cons_cons, List.pairwise_cons]
    refine ⟨?_, pairwise_zipWith_right g hg as bs h.2⟩
    intro c hc
    obtain ⟨a', b', hb', rfl⟩ := mem_zipWith_right g as bs hc
    exact hg a a' b b' (h.1 b' hb')

theorem forall₂_zipWith_of_forall₂ {α β γ : Type*} (g : α → β → γ) {R : α → β → Prop}
    {Q : α → γ → Prop} (hQ : ∀ a b, R a b → Q a (g a b)) :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → List.Forall₂ Q as (List.zipWith g as bs)
  | [], [], _ => List.Forall₂.nil
  | a :: as, b :: bs, h => by
    rw [List.forall₂_cons] at h
    rw [List.zipWith_cons_cons]
    exact List.Forall₂.cons (hQ a b h.1) (forall₂_zipWith_of_forall₂ g hQ h.2)

theorem mem_foldr_union {α : Type*} [DecidableEq α] :
    ∀ (l : List (Finset α)) {x : α}, x ∈ l.foldr (· ∪ ·) ∅ → ∃ A ∈ l, x ∈ A
  | [], _, h => absurd h (Finset.notMem_empty _)
  | A :: l, x, h => by
    rw [List.foldr_cons, Finset.mem_union] at h
    rcases h with h | h
    · exact ⟨A, List.mem_cons_self .., h⟩
    · obtain ⟨B, hB, hx⟩ := mem_foldr_union l h
      exact ⟨B, List.mem_cons_of_mem _ hB, hx⟩

theorem forall₂_imp_mem {α β : Type*} {R S : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, (∀ a ∈ as, ∀ b ∈ bs, R a b → S a b) →
      List.Forall₂ R as bs → List.Forall₂ S as bs
  | [], [], _, _ => List.Forall₂.nil
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | a :: as, b :: bs, hRS, h => by
    rw [List.forall₂_cons] at h
    exact List.Forall₂.cons (hRS a (List.mem_cons_self ..) b (List.mem_cons_self ..) h.1)
      (forall₂_imp_mem (fun a' ha' b' hb' => hRS a' (List.mem_cons_of_mem _ ha') b'
        (List.mem_cons_of_mem _ hb')) h.2)

theorem forall₂_mem_left {α β : Type*} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {a}, a ∈ as → ∃ b ∈ bs, R a b
  | [], [], _, _, h => nomatch h
  | a :: as, b :: bs, h, a', ha' => by
    rw [List.forall₂_cons] at h
    rw [List.mem_cons] at ha'
    rcases ha' with rfl | ha'
    · exact ⟨b, List.mem_cons_self .., h.1⟩
    · obtain ⟨b', hb', hr⟩ := forall₂_mem_left h.2 ha'
      exact ⟨b', List.mem_cons_of_mem _ hb', hr⟩

theorem pairwise_flatMap_of {α β : Type*} {R : β → β → Prop} (g : α → List β) :
    ∀ L : List α, (∀ x ∈ L, (g x).Pairwise R) →
      L.Pairwise (fun x y => ∀ a ∈ g x, ∀ b ∈ g y, R a b) → (L.flatMap g).Pairwise R
  | [], _, _ => List.Pairwise.nil
  | x :: L, hin, hout => by
    rw [List.pairwise_cons] at hout
    rw [List.flatMap_cons, List.pairwise_append]
    refine ⟨hin x (List.mem_cons_self ..), pairwise_flatMap_of g L
      (fun y hy => hin y (List.mem_cons_of_mem _ hy)) hout.2, ?_⟩
    intro a ha b hb
    rw [List.mem_flatMap] at hb
    obtain ⟨y, hy, hb⟩ := hb
    exact hout.1 y hy a ha b hb

/-! ### Instances -/

/-- The specification side of an instance: what the construction denotes, what a trace is, and
    the obligations the paper leaves to each instance. -/
structure Instance (Op Tau : Type*) extends Traced Op Tau where
  /-- Partial candidates built at a node, each with the variables it owns. -/
  candidates : Node Op → Finset Assign
  /-- Trace of a partial candidate at a node. -/
  trace : Node Op → Assign → Tau
  /-- Well-formed constructions: the ones the obligations below are about (a decomposition
      assigns each variable in one place; an arbitrary `Node` need not). -/
  WF : Node Op → Prop
  wf_children : ∀ (op : Op) (cs : List (Node Op)), WF (.mk op cs) → ∀ c ∈ cs, WF c
  /-- Variables the candidates of a node assign (`dom` in Definition 10). -/
  nodeDom : Node Op → Finset Var
  dom_eq : ∀ n, WF n → ∀ f ∈ candidates n, f.dom = nodeDom n
  /-- Variables an operation owns itself; the children's are pairwise disjoint and disjoint
      from them. -/
  owned : Op → Finset Var
  owned_disjoint : ∀ (op : Op) (cs : List (Node Op)), WF (.mk op cs) →
    ∀ c ∈ cs, Disjoint (owned op) (nodeDom c)
  children_disjoint : ∀ (op : Op) (cs : List (Node Op)), WF (.mk op cs) →
    (cs.map nodeDom).Pairwise Disjoint
  /-- Every output of `step` assigns exactly the owned variables, each once. -/
  step_leaves : ∀ (op : Op) (taus : List Tau), ∀ out ∈ step op taus,
    (out.2.map Prod.fst).Nodup ∧ (out.2.map Prod.fst).toFinset = owned op
  /-- Distinct outputs assign the owned variables differently. -/
  step_nodup : ∀ (op : Op) (taus : List Tau),
    ((step op taus).map fun out => Assign.ofList out.2).Nodup
  /-- Obligation 3: the candidates at a node are the joins of one candidate per child with the
      leaves `step` yields for their traces, and `step` names their trace. -/
  cand_iff : ∀ (op : Op) (cs : List (Node Op)), WF (.mk op cs) → ∀ f : Assign,
    f ∈ candidates (.mk op cs) ↔
    ∃ fs : List Assign, List.Forall₂ (fun f c => f ∈ candidates c) fs cs ∧
      ∃ out ∈ step op (List.zipWith trace cs fs),
        f = (Assign.joinAll fs).join (Assign.ofList out.2)
  trace_mk : ∀ (op : Op) (cs : List (Node Op)) (fs : List Assign) (out : Tau × List (Var × Val)),
    WF (.mk op cs) → List.Forall₂ (fun f c => f ∈ candidates c) fs cs →
    out ∈ step op (List.zipWith trace cs fs) →
    trace (.mk op cs) ((Assign.joinAll fs).join (Assign.ofList out.2)) = out.1
  /-- Obligation 2: solutionhood from the trace alone. -/
  solution : Node Op → Assign → Prop
  accept_iff : ∀ n f, f ∈ candidates n → (solution n f ↔ accept (trace n f) = true)

namespace Instance
open Traced
variable {Op Tau : Type*} [DecidableEq Tau] (I : Instance Op Tau)

/-- The candidates of a node with a given trace: what a row should denote. -/
def rowSet (n : Node Op) (τ : Tau) : Finset Assign :=
  (I.candidates n).filter fun f => I.trace n f = τ

theorem rowSet_disjoint (n : Node Op) {τ τ' : Tau} (h : τ ≠ τ') :
    Disjoint (I.rowSet n τ) (I.rowSet n τ') := by
  rw [Finset.disjoint_left]
  intro f hf hf'
  rw [rowSet, Finset.mem_filter] at hf hf'
  exact h (hf.2.symm.trans hf'.2)

omit [DecidableEq Tau] in
theorem children_pairwise {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs)) :
    cs.Pairwise fun c c' => Disjoint (I.nodeDom c) (I.nodeDom c') :=
  List.pairwise_map.mp (I.children_disjoint op cs hwf)

omit [DecidableEq Tau] in
theorem children_pairwise_wf {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs)) :
    cs.Pairwise fun c c' => I.WF c ∧ I.WF c' ∧ Disjoint (I.nodeDom c) (I.nodeDom c') :=
  List.Pairwise.imp_of_mem
    (fun {c c'} hc hc' h => ⟨I.wf_children op cs hwf c hc, I.wf_children op cs hwf c' hc', h⟩)
    (I.children_pairwise hwf)

omit [DecidableEq Tau] in
/-- Restricting a join of one candidate per child to a child's variables recovers that
    candidate. -/
theorem restrict_foldl_join_cand :
    ∀ {fs : List Assign} {cs : List (Node Op)}, List.Forall₂ (fun f c => f ∈ I.candidates c) fs cs →
      (∀ c ∈ cs, I.WF c) →
      cs.Pairwise (fun c c' => Disjoint (I.nodeDom c) (I.nodeDom c')) →
      ∀ e : Assign, (∀ c ∈ cs, Disjoint e.dom (I.nodeDom c)) →
      List.Forall₂ (fun f c => (fs.foldl Assign.join e).restrict (I.nodeDom c) = f) fs cs
  | [], [], _, _, _, _, _ => List.Forall₂.nil
  | f :: fs, c :: cs, hF, hcs, hpair, e, he => by
    rw [List.forall₂_cons] at hF
    rw [List.pairwise_cons] at hpair
    rw [List.foldl_cons]
    have hfd : f.dom = I.nodeDom c := I.dom_eq c (hcs c (List.mem_cons_self ..)) f hF.1
    refine List.Forall₂.cons ?_ ?_
    · rw [Assign.restrict_foldl_join fs (e.join f)]
      · rw [Assign.restrict_join_of_disjoint_left (he c (List.mem_cons_self ..)).symm, ← hfd,
          Assign.restrict_dom_self]
      · intro g hg
        obtain ⟨c', hc', hgc'⟩ := forall₂_mem_left hF.2 hg
        rw [I.dom_eq c' (hcs c' (List.mem_cons_of_mem _ hc')) g hgc']
        exact hpair.1 c' hc'
    · apply restrict_foldl_join_cand hF.2 (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        hpair.2 (e.join f)
      intro c' hc'
      apply Finset.disjoint_of_subset_left (Assign.join_dom_subset e f)
      rw [Finset.disjoint_union_left]
      exact ⟨he c' (List.mem_cons_of_mem _ hc'), hfd ▸ hpair.1 c' hc'⟩

omit [DecidableEq Tau] in
theorem restrict_joinAll {op : Op} {fs : List Assign} {cs : List (Node Op)}
    (hwf : I.WF (.mk op cs)) (hF : List.Forall₂ (fun f c => f ∈ I.candidates c) fs cs) :
    List.Forall₂ (fun f c => (Assign.joinAll fs).restrict (I.nodeDom c) = f) fs cs :=
  I.restrict_foldl_join_cand hF (I.wf_children op cs hwf) (I.children_pairwise hwf) Assign.empty
    (fun _ _ => by rw [Assign.empty_dom]; exact Finset.disjoint_empty_left _)

/-- The children's tables, as the induction hypothesis provides them. -/
def TablesSem (tables : List (Table Tau)) (cs : List (Node Op)) : Prop :=
  List.Forall₂ (fun T c => TableSem T (I.rowSet c) ∧ (T.map Prod.fst).Nodup) tables cs

/-- One row from each child denotes that child's candidates with the row's trace. -/
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

/-- The denotation of one item: one candidate per child with the rows' traces, joined with the
    leaves of one `step` output. -/
def itemSet (cs : List (Node Op)) (rows : List (Tau × Expr)) (out : Tau × List (Var × Val)) :
    Finset Assign :=
  (joinedSet (List.zipWith (fun r c => I.rowSet c r.1) rows cs)).image fun f =>
    f.join (Assign.ofList out.2)

theorem joined_sem {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {tables : List (Table Tau)} (hT : I.TablesSem tables cs) {rows : List (Tau × Expr)}
    (hrows : List.Forall₂ (· ∈ ·) rows tables) :
    Sem (joined rows) (joinedSet (List.zipWith (fun r c => I.rowSet c r.1) rows cs)) := by
  have hrs := I.rows_sem hrows hT
  apply Sem.joined
  · exact forall₂_zipWith_of_forall₂ (fun (r : Tau × Expr) (c : Node Op) => I.rowSet c r.1)
      (fun _ _ h => h) hrs
  · apply pairwise_zipWith_right
      (P := fun c c' => I.WF c ∧ I.WF c' ∧ Disjoint (I.nodeDom c) (I.nodeDom c')) _ _
      rows cs (I.children_pairwise_wf hwf)
    intro r r' c c' ⟨hc, hc', hcc'⟩ f hf g hg
    rw [rowSet, Finset.mem_filter] at hf hg
    rw [I.dom_eq c hc f hf.1, I.dom_eq c' hc' g hg.1]
    exact hcc'

/-- A variable of a join of child candidates belongs to one of the children. -/
theorem mem_dom_joinAll {cs : List (Node Op)} (hcs : ∀ c ∈ cs, I.WF c) {rows : List (Tau × Expr)}
    {fs : List Assign}
    (hfs : List.Forall₂ (· ∈ ·) fs (List.zipWith (fun r c => I.rowSet c r.1) rows cs)) {x : Var}
    (hx : x ∈ (Assign.joinAll fs).dom) : ∃ c ∈ cs, x ∈ I.nodeDom c := by
  unfold Assign.joinAll at hx
  have hsub := Assign.dom_foldl_join_subset fs Assign.empty hx
  rw [Assign.empty_dom, Finset.empty_union] at hsub
  obtain ⟨D, hD, hxD⟩ := mem_foldr_union _ hsub
  rw [List.mem_map] at hD
  obtain ⟨g, hg, rfl⟩ := hD
  obtain ⟨A, hA, hgA⟩ := forall₂_mem_left hfs hg
  obtain ⟨r, c, hc, rfl⟩ := mem_zipWith_right _ rows cs hA
  rw [rowSet, Finset.mem_filter] at hgA
  exact ⟨c, hc, I.dom_eq c (hcs c hc) g hgA.1 ▸ hxD⟩

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
  have hq_owned : q.1 ∈ I.owned op := by
    rw [← hvars, List.mem_toFinset]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  exact Finset.disjoint_left.mp (I.owned_disjoint op cs hwf c hc) hq_owned hqc

omit [DecidableEq Tau] in
/-- The leaves of an output, as an assignment, assign exactly the owned variables. -/
theorem ofList_dom_owned {op : Op} {taus : List Tau} {out : Tau × List (Var × Val)}
    (hout : out ∈ I.step op taus) : (Assign.ofList out.2).dom = I.owned op := by
  obtain ⟨hnd, hvars⟩ := I.step_leaves op taus out hout
  rw [Assign.ofList_dom _ hnd, hvars]

/-- A member of an item restricts to the output's leaves on the owned variables. -/
theorem restrict_owned_of_mem_itemSet {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {rows : List (Tau × Expr)}
    {out : Tau × List (Var × Val)} (hout : out ∈ I.step op (rows.map Prod.fst)) {f : Assign}
    (hf : f ∈ I.itemSet cs rows out) : f.restrict (I.owned op) = Assign.ofList out.2 := by
  rw [itemSet, Finset.mem_image] at hf
  obtain ⟨a, ha, rfl⟩ := hf
  rw [mem_joinedSet] at ha
  obtain ⟨fs, hfs, rfl⟩ := ha
  have hd : Disjoint (Assign.joinAll fs).dom (Assign.ofList out.2).dom := by
    rw [I.ofList_dom_owned hout, Finset.disjoint_left]
    intro x hx hxo
    obtain ⟨c, hc, hxc⟩ := I.mem_dom_joinAll (I.wf_children op cs hwf) hfs hx
    exact Finset.disjoint_left.mp (I.owned_disjoint op cs hwf c hc) hxo hxc
  rw [← I.ofList_dom_owned hout]
  exact Assign.join_restrict_right hd

/-- Restricting a join of one candidate per child (with the rows' traces) to a child's variables
    gives a candidate of that child with that row's trace. -/
theorem restrict_foldl_join_rows :
    ∀ (rows : List (Tau × Expr)) (cs : List (Node Op)) (fs : List Assign),
      List.Forall₂ (· ∈ ·) fs (List.zipWith (fun r c => I.rowSet c r.1) rows cs) →
      rows.length = cs.length → (∀ c ∈ cs, I.WF c) →
      cs.Pairwise (fun c c' => Disjoint (I.nodeDom c) (I.nodeDom c')) →
      ∀ e : Assign, (∀ c ∈ cs, Disjoint e.dom (I.nodeDom c)) →
      List.Forall₂ (fun r c => (fs.foldl Assign.join e).restrict (I.nodeDom c) ∈ I.rowSet c r.1)
        rows cs
  | [], [], _, _, _, _, _, _, _ => List.Forall₂.nil
  | [], _ :: _, _, _, hlen, _, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _, _, _, _ => by simp at hlen
  | r :: rows, c :: cs, fs, hfs, hlen, hcs, hpair, e, he => by
    rw [List.zipWith_cons_cons] at hfs
    cases hfs with
    | cons hf hfs =>
      rename_i f fs
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [List.pairwise_cons] at hpair
      rw [List.foldl_cons]
      have hf' := hf
      rw [rowSet, Finset.mem_filter] at hf'
      have hfd : f.dom = I.nodeDom c := I.dom_eq c (hcs c (List.mem_cons_self ..)) f hf'.1
      refine List.Forall₂.cons ?_ ?_
      · rw [Assign.restrict_foldl_join fs (e.join f)]
        · rw [Assign.restrict_join_of_disjoint_left (he c (List.mem_cons_self ..)).symm, ← hfd,
            Assign.restrict_dom_self]
          exact hf
        · intro g hg
          obtain ⟨A, hA, hgA⟩ := forall₂_mem_left hfs hg
          obtain ⟨r', c', hc', rfl⟩ := mem_zipWith_right _ rows cs hA
          rw [rowSet, Finset.mem_filter] at hgA
          rw [I.dom_eq c' (hcs c' (List.mem_cons_of_mem _ hc')) g hgA.1]
          exact hpair.1 c' hc'
      · apply restrict_foldl_join_rows rows cs fs hfs hlen
          (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hpair.2 (e.join f)
        intro c' hc'
        apply Finset.disjoint_of_subset_left (Assign.join_dom_subset e f)
        rw [Finset.disjoint_union_left]
        exact ⟨he c' (List.mem_cons_of_mem _ hc'), hfd ▸ hpair.1 c' hc'⟩

/-- A member of an item restricts, on each child's variables, to a candidate of that child with
    the row's trace. -/
theorem restrict_children_of_mem_itemSet {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {rows : List (Tau × Expr)} (hlen : rows.length = cs.length) {out : Tau × List (Var × Val)}
    (hout : out ∈ I.step op (rows.map Prod.fst)) {f : Assign} (hf : f ∈ I.itemSet cs rows out) :
    List.Forall₂ (fun r c => f.restrict (I.nodeDom c) ∈ I.rowSet c r.1) rows cs := by
  rw [itemSet, Finset.mem_image] at hf
  obtain ⟨a, ha, rfl⟩ := hf
  rw [mem_joinedSet] at ha
  obtain ⟨fs, hfs, rfl⟩ := ha
  have hres := I.restrict_foldl_join_rows rows cs fs hfs hlen (I.wf_children op cs hwf)
    (I.children_pairwise hwf)
    Assign.empty (fun _ _ => by rw [Assign.empty_dom]; exact Finset.disjoint_empty_left _)
  refine forall₂_imp_mem ?_ hres
  intro r _ c hc h
  -- the leaves' variables are owned by `op`, away from any child
  rw [Assign.restrict_join_of_disjoint_right]
  · exact h
  · rw [I.ofList_dom_owned hout]
    exact (I.owned_disjoint op cs hwf c hc).symm

/-- Two tuples of rows that agree on where one assignment restricts are the same tuple. -/
theorem rows_eq_of_restrict {f : Assign} {tables : List (Table Tau)} {cs : List (Node Op)}
    (hT : I.TablesSem tables cs) :
    ∀ {rows rows' : List (Tau × Expr)}, List.Forall₂ (· ∈ ·) rows tables →
      List.Forall₂ (· ∈ ·) rows' tables →
      List.Forall₂ (fun r c => f.restrict (I.nodeDom c) ∈ I.rowSet c r.1) rows cs →
      List.Forall₂ (fun r c => f.restrict (I.nodeDom c) ∈ I.rowSet c r.1) rows' cs →
      rows = rows' := by
  induction hT with
  | nil =>
    intro rows rows' h1 h2 _ _
    cases h1
    cases h2
    rfl
  | cons hTc _ ih =>
    intro rows rows' h1 h2 h3 h4
    cases h1 with
    | cons hr h1 =>
      cases h2 with
      | cons hr' h2 =>
        cases h3 with
        | cons hp h3 =>
          cases h4 with
          | cons hp' h4 =>
            congr 1
            · apply eq_of_mem_of_fst_eq hTc.2 hr hr'
              by_contra hne
              exact Finset.disjoint_left.mp (I.rowSet_disjoint _ hne) hp hp'
            · exact ih h1 h2 h3 h4

/-- Items of one tuple with different leaves are disjoint. -/
theorem itemSet_disjoint_of_ne_leaves {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {rows : List (Tau × Expr)}
    {out out' : Tau × List (Var × Val)} (hout : out ∈ I.step op (rows.map Prod.fst))
    (hout' : out' ∈ I.step op (rows.map Prod.fst))
    (hne : Assign.ofList out.2 ≠ Assign.ofList out'.2) :
    Disjoint (I.itemSet cs rows out) (I.itemSet cs rows out') := by
  rw [Finset.disjoint_left]
  intro f hf hf'
  exact hne ((I.restrict_owned_of_mem_itemSet hwf hout hf).symm.trans
    (I.restrict_owned_of_mem_itemSet hwf hout' hf'))

/-- Items of different tuples are disjoint. -/
theorem itemSet_disjoint_of_ne_rows {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {tables : List (Table Tau)} (hT : I.TablesSem tables cs) {rows rows' : List (Tau × Expr)}
    (hrows : List.Forall₂ (· ∈ ·) rows tables) (hrows' : List.Forall₂ (· ∈ ·) rows' tables)
    (hne : rows ≠ rows') {out out' : Tau × List (Var × Val)}
    (hout : out ∈ I.step op (rows.map Prod.fst)) (hout' : out' ∈ I.step op (rows'.map Prod.fst)) :
    Disjoint (I.itemSet cs rows out) (I.itemSet cs rows' out') := by
  rw [Finset.disjoint_left]
  intro f hf hf'
  have hlen : tables.length = cs.length := List.Forall₂.length_eq hT
  apply hne
  exact I.rows_eq_of_restrict hT hrows hrows'
    (I.restrict_children_of_mem_itemSet hwf ((List.Forall₂.length_eq hrows).trans hlen) hout hf)
    (I.restrict_children_of_mem_itemSet hwf ((List.Forall₂.length_eq hrows').trans hlen) hout'
      hf')

/-- One assignment per zipped row set is one candidate per child, with the rows' traces. -/
theorem cand_of_zip :
    ∀ (rows : List (Tau × Expr)) (cs : List (Node Op)) (fs : List Assign),
      rows.length = cs.length →
      List.Forall₂ (· ∈ ·) fs (List.zipWith (fun r c => I.rowSet c r.1) rows cs) →
      List.Forall₂ (fun f c => f ∈ I.candidates c) fs cs ∧
        rows.map Prod.fst = List.zipWith I.trace cs fs
  | [], [], _, _, hfs => by
    cases hfs
    exact ⟨List.Forall₂.nil, rfl⟩
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | r :: rows, c :: cs, fs, hlen, hfs => by
    rw [List.zipWith_cons_cons] at hfs
    cases hfs with
    | cons hf hfs =>
      rename_i f fs
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [rowSet, Finset.mem_filter] at hf
      obtain ⟨ih1, ih2⟩ := cand_of_zip rows cs fs hlen hfs
      refine ⟨List.Forall₂.cons hf.1 ih1, ?_⟩
      rw [List.map_cons, List.zipWith_cons_cons, ih2, hf.2]

/-- For one candidate per child there is a tuple of rows, one from each table, with their
    traces. -/
theorem exists_rows {tables : List (Table Tau)} {cs : List (Node Op)} (hT : I.TablesSem tables cs) :
    ∀ {fs : List Assign}, List.Forall₂ (fun f c => f ∈ I.candidates c) fs cs →
      ∃ rows : List (Tau × Expr), List.Forall₂ (· ∈ ·) rows tables ∧
        rows.map Prod.fst = List.zipWith I.trace cs fs ∧
        List.Forall₂ (· ∈ ·) fs (List.zipWith (fun r c => I.rowSet c r.1) rows cs) := by
  induction hT with
  | nil =>
    intro fs hfs
    cases hfs
    exact ⟨[], List.Forall₂.nil, rfl, List.Forall₂.nil⟩
  | @cons T c tables cs hTc _ ih =>
    intro fs hfs
    cases hfs with
    | @cons f _ fs _ hf hfs =>
      obtain ⟨rows, h1, h2, h3⟩ := ih hfs
      have hfr : f ∈ I.rowSet c (I.trace c f) := by
        rw [rowSet, Finset.mem_filter]
        exact ⟨hf, rfl⟩
      have hne : rowExpr T (I.trace c f) ≠ .empty :=
        Sem.ne_empty (hTc.1 (I.trace c f)) ⟨f, hfr⟩
      refine ⟨(I.trace c f, rowExpr T (I.trace c f)) :: rows,
        List.Forall₂.cons (mem_of_rowExpr_ne hne) h1, ?_, ?_⟩
      · rw [List.map_cons, List.zipWith_cons_cons, h2]
      · rw [List.zipWith_cons_cons]
        exact List.Forall₂.cons hfr h3

/-- Claim 1, one step: the children's tables give the node's table. -/
theorem stepNode_sound {op : Op} {cs : List (Node Op)} (hwf : I.WF (.mk op cs))
    {tables : List (Table Tau)} (hT : I.TablesSem tables cs) :
    TableSem (stepNode I.toTraced op tables) (I.rowSet (.mk op cs)) := by
  rw [stepNode_eq_foldl]
  have hlen : tables.length = cs.length := List.Forall₂.length_eq hT
  -- every item comes from a tuple of rows and a step output
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
  -- members of items are candidates of the node, with the output's trace
  have hcand : ∀ rows, List.Forall₂ (· ∈ ·) rows tables → ∀ out ∈ I.step op (rows.map Prod.fst),
      ∀ f ∈ I.itemSet cs rows out,
        f ∈ I.candidates (.mk op cs) ∧ I.trace (.mk op cs) f = out.1 := by
    intro rows hrows out hout f hf
    rw [itemSet, Finset.mem_image] at hf
    obtain ⟨a, ha, rfl⟩ := hf
    rw [mem_joinedSet] at ha
    obtain ⟨fs, hfs, rfl⟩ := ha
    obtain ⟨hc, htr⟩ := I.cand_of_zip rows cs fs ((List.Forall₂.length_eq hrows).trans hlen) hfs
    rw [htr] at hout
    exact ⟨(I.cand_iff op cs hwf _).mpr ⟨fs, hc, out, hout, rfl⟩,
      I.trace_mk op cs fs out hwf hc hout⟩
  -- the rows' table is exactly the node's candidates by trace
  have hset : ∀ τ, itemsSet (fun it => denot it.2) ((tuples tables).flatMap (rowItems I.toTraced op)) τ
      = I.rowSet (.mk op cs) τ := by
    intro τ
    ext f
    rw [mem_itemsSet, rowSet, Finset.mem_filter]
    constructor
    · rintro ⟨it, hit, hτ, hf⟩
      rw [hmem] at hit
      obtain ⟨rows, hrows, out, hout, rfl⟩ := hit
      rw [hden rows hrows out hout] at hf
      have h := hcand rows hrows out hout f hf
      exact ⟨h.1, h.2.trans hτ⟩
    · rintro ⟨hf, hτ⟩
      obtain ⟨fs, hc, out, hout, rfl⟩ := (I.cand_iff op cs hwf f).mp hf
      obtain ⟨rows, hrows, htr, hfs⟩ := I.exists_rows hT hc
      have hout' : out ∈ I.step op (rows.map Prod.fst) := by rw [htr]; exact hout
      refine ⟨(out.1, Expr.joinLeaves (joined rows) out.2), ?_, ?_, ?_⟩
      · rw [hmem]
        exact ⟨rows, hrows, out, hout', rfl⟩
      · show out.1 = τ
        rw [← hτ, I.trace_mk op cs fs out hwf hc hout]
      · show _ ∈ denot (Expr.joinLeaves (joined rows) out.2)
        rw [hden rows hrows out hout', itemSet, Finset.mem_image]
        exact ⟨Assign.joinAll fs, (mem_joinedSet _ _).mpr ⟨fs, hfs, rfl⟩, rfl⟩
  have key := TableSem.foldl_unionInto (Dn := I.nodeDom (.mk op cs)) (fun it => denot it.2)
    ((tuples tables).flatMap (rowItems I.toTraced op)) (T := []) (S := fun _ => ∅)
    (fun _ => Sem.empty) ?_ ?_ ?_ ?_ ?_
  · intro τ
    have h := key τ
    simp only [Finset.empty_union] at h
    rw [hset τ] at h
    exact h
  · -- every item denotes
    intro it hit
    rw [hmem] at hit
    obtain ⟨rows, hrows, out, hout, rfl⟩ := hit
    show Sem (Expr.joinLeaves (joined rows) out.2) (denot (Expr.joinLeaves (joined rows) out.2))
    rw [hden rows hrows out hout]
    exact I.item_sem hwf hT hrows hout
  · -- items are pairwise disjoint
    apply pairwise_flatMap_of
    · intro rows hrows
      have hrows' := mem_tuples.mp hrows
      rw [rowItems, List.pairwise_map]
      have hs : (I.step op (rows.map Prod.fst)).Pairwise
          (fun o o' => Assign.ofList o.2 ≠ Assign.ofList o'.2) :=
        List.pairwise_map.mp (I.step_nodup op (rows.map Prod.fst))
      refine List.Pairwise.imp_of_mem ?_ hs
      intro o o' ho ho' hne
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
      intro rows rows' hr hr' hne a ha b hb
      rw [rowItems, List.mem_map] at ha hb
      obtain ⟨o, ho, rfl⟩ := ha
      obtain ⟨o', ho', rfl⟩ := hb
      show Disjoint (denot (Expr.joinLeaves (joined rows) o.2))
        (denot (Expr.joinLeaves (joined rows') o'.2))
      rw [hden rows (mem_tuples.mp hr) o ho, hden rows' (mem_tuples.mp hr') o' ho']
      exact I.itemSet_disjoint_of_ne_rows hwf hT (mem_tuples.mp hr)
        (mem_tuples.mp hr') hne ho ho'
  · intro it _
    exact Finset.disjoint_empty_left _
  · intro it hit f hf
    rw [hmem] at hit
    obtain ⟨rows, hrows, out, hout, rfl⟩ := hit
    change f ∈ denot (Expr.joinLeaves (joined rows) out.2) at hf
    rw [hden rows hrows out hout] at hf
    exact I.dom_eq _ hwf f (hcand rows hrows out hout f hf).1
  · intro τ f hf
    exact absurd hf (Finset.notMem_empty f)

end Instance

namespace Instance
variable {Op Tau : Type*} [DecidableEq Tau]

mutual
/-- Claim 1 at every node: the table of `run` denotes the candidates by trace, with distinct
    traces. -/
theorem run_sound (I : Instance Op Tau) :
    ∀ n : Node Op, I.WF n →
      Traced.TableSem (Traced.run I.toTraced n) (I.rowSet n) ∧
        ((Traced.run I.toTraced n).map Prod.fst).Nodup
  | .mk op cs, hwf => by
    rw [Traced.run]
    exact ⟨I.stepNode_sound hwf (runList_sound I cs (I.wf_children op cs hwf)),
      Traced.stepNode_nodup _ _ _⟩
theorem runList_sound (I : Instance Op Tau) :
    ∀ cs : List (Node Op), (∀ c ∈ cs, I.WF c) → I.TablesSem (Traced.runList I.toTraced cs) cs
  | [], _ => List.Forall₂.nil
  | c :: cs, hcs => by
    rw [Traced.runList]
    exact List.Forall₂.cons (run_sound I c (hcs c (List.mem_cons_self ..)))
      (runList_sound I cs fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
end

end Instance

namespace Traced
variable {Op Tau : Type*} [DecidableEq Tau]

/-- The accepted rows of a list, as a set. -/
def acceptedSet (I : Traced Op Tau) (S : Tau → Finset Assign) (L : List (Tau × Expr)) :
    Finset Assign :=
  (L.filter fun row => I.accept row.1).foldr (fun row acc => S row.1 ∪ acc) ∅

omit [DecidableEq Tau] in
theorem acceptedSet_cons (I : Traced Op Tau) (S : Tau → Finset Assign) (row : Tau × Expr)
    (L : List (Tau × Expr)) :
    acceptedSet I S (row :: L) =
      if I.accept row.1 = true then S row.1 ∪ acceptedSet I S L else acceptedSet I S L := by
  unfold acceptedSet
  rw [List.filter_cons]
  by_cases h : I.accept row.1 = true
  · simp [h]
  · simp [h]

omit [DecidableEq Tau] in
theorem mem_acceptedSet (I : Traced Op Tau) (S : Tau → Finset Assign) :
    ∀ (L : List (Tau × Expr)) (f : Assign),
      f ∈ acceptedSet I S L ↔ ∃ row ∈ L, I.accept row.1 = true ∧ f ∈ S row.1
  | [], f => by simp [acceptedSet]
  | row :: L, f => by
    rw [acceptedSet_cons]
    by_cases h : I.accept row.1 = true
    · rw [ite_eq_left h, Finset.mem_union, mem_acceptedSet I S L]
      constructor
      · rintro (hf | ⟨r, hr, ha, hf⟩)
        · exact ⟨row, List.mem_cons_self .., h, hf⟩
        · exact ⟨r, List.mem_cons_of_mem _ hr, ha, hf⟩
      · rintro ⟨r, hr, ha, hf⟩
        rw [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact Or.inl hf
        · exact Or.inr ⟨r, hr, ha, hf⟩
    · rw [ite_eq_right h, mem_acceptedSet I S L]
      constructor
      · rintro ⟨r, hr, ha, hf⟩
        exact ⟨r, List.mem_cons_of_mem _ hr, ha, hf⟩
      · rintro ⟨r, hr, ha, hf⟩
        rw [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact absurd ha h
        · exact ⟨r, hr, ha, hf⟩

omit [DecidableEq Tau] in
/-- Folding `union'` over the accepted rows of a table whose rows denote pairwise disjoint sets
    of one domain. -/
theorem Sem.foldl_accept {Dn : Finset Var} (I : Traced Op Tau) (S : Tau → Finset Assign)
    (hS : ∀ τ τ', τ ≠ τ' → Disjoint (S τ) (S τ')) (hdom : ∀ τ, ∀ f ∈ S τ, f.dom = Dn) :
    ∀ (L : List (Tau × Expr)) (e : Expr) (A : Finset Assign), Sem e A →
      (L.map Prod.fst).Nodup → (∀ row ∈ L, Sem row.2 (S row.1)) →
      (∀ row ∈ L, Disjoint A (S row.1)) → (∀ f ∈ A, f.dom = Dn) →
      Sem (L.foldl (fun e row => if I.accept row.1 then Expr.union' e row.2 else e) e)
        (A ∪ acceptedSet I S L)
  | [], e, A, he, _, _, _, _ => by simpa [acceptedSet] using he
  | row :: L, e, A, he, hnd, hL, hA, hAd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    have hdisjL : ∀ r ∈ L, Disjoint (S row.1) (S r.1) := by
      intro r hr
      apply hS
      intro heq
      exact hnd.1 (heq ▸ List.mem_map.mpr ⟨r, hr, rfl⟩)
    by_cases h : I.accept row.1 = true
    · rw [ite_eq_left h]
      have ih := Sem.foldl_accept (Dn := Dn) I S hS hdom L (Expr.union' e row.2) (A ∪ S row.1)
        (Sem.union' he (hL row (List.mem_cons_self ..)) (hA row (List.mem_cons_self ..))
          (fun f hf g hg => by rw [hAd f hf, hdom _ g hg]))
        hnd.2 (fun r hr => hL r (List.mem_cons_of_mem _ hr))
        (fun r hr => Finset.disjoint_union_left.mpr
          ⟨hA r (List.mem_cons_of_mem _ hr), hdisjL r hr⟩)
        (fun f hf => by
          rw [Finset.mem_union] at hf
          rcases hf with hf | hf
          · exact hAd f hf
          · exact hdom _ f hf)
      rw [acceptedSet_cons, ite_eq_left h, ← Finset.union_assoc]
      exact ih
    · rw [ite_eq_right h]
      rw [acceptedSet_cons, ite_eq_right h]
      exact Sem.foldl_accept (Dn := Dn) I S hS hdom L e A he hnd.2
        (fun r hr => hL r (List.mem_cons_of_mem _ hr))
        (fun r hr => hA r (List.mem_cons_of_mem _ hr)) hAd

end Traced

/-- Claim 1 at the root: on a well-formed construction, the DP's output denotes exactly the
    solution set. -/
theorem solve_sound {Op Tau : Type*} [DecidableEq Tau] (I : Instance Op Tau) {n : Node Op}
    (hwf : I.WF n) :
    Sem (I.toTraced.solve n) ((I.candidates n).filter fun f => I.accept (I.trace n f) = true) := by
  obtain ⟨hT, hnd⟩ := I.run_sound n hwf
  unfold Traced.solve
  have h := Traced.Sem.foldl_accept (Dn := I.nodeDom n) I.toTraced (I.rowSet n)
    (fun τ τ' hne => I.rowSet_disjoint n hne)
    (fun τ f hf => I.dom_eq n hwf f (Finset.mem_filter.mp hf).1)
    (Traced.run I.toTraced n) .empty ∅ Sem.empty hnd
    (fun row hr => by
      have := hT row.1
      rwa [Traced.rowExpr_of_mem hnd (show (row.1, row.2) ∈ _ from hr)] at this)
    (fun _ _ => Finset.disjoint_empty_left _) (fun f hf => absurd hf (Finset.notMem_empty f))
  rw [Finset.empty_union] at h
  have hset : Traced.acceptedSet I.toTraced (I.rowSet n) (Traced.run I.toTraced n) =
      (I.candidates n).filter fun f => I.accept (I.trace n f) = true := by
    ext f
    rw [Traced.mem_acceptedSet, Finset.mem_filter]
    constructor
    · rintro ⟨row, _, ha, hf⟩
      rw [Instance.rowSet, Finset.mem_filter] at hf
      exact ⟨hf.1, hf.2 ▸ ha⟩
    · rintro ⟨hf, ha⟩
      have hfr : f ∈ I.rowSet n (I.trace n f) := by
        rw [Instance.rowSet, Finset.mem_filter]
        exact ⟨hf, rfl⟩
      have hne := Sem.ne_empty (hT (I.trace n f)) ⟨f, hfr⟩
      exact ⟨(I.trace n f, Traced.rowExpr (Traced.run I.toTraced n) (I.trace n f)),
        Traced.mem_of_rowExpr_ne hne, ha, hfr⟩
  rw [hset] at h
  exact h

end Formalism
