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
  rw [dif_pos (⟨A, h⟩ : ∃ A, Sem e A)]
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

/-- Mirrors `scheme::step_node`: one row from each child, every way (`List.sections`); each
    `(trace, leaves)` the step yields joins the leaves onto the children's expressions and goes
    into the row of that trace. -/
def stepNode (I : Traced Op Tau) (op : Op) (tables : List (Table Tau)) : Table Tau :=
  tables.sections.foldl
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
    · rw [if_neg (Ne.symm h), if_neg h]
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
  · rw [if_pos h, if_pos h]
    exact Sem.union' (hT tau) he hdisj hdom
  · rw [if_neg h, if_neg h]
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
        · simp only [heq, if_true]
          exact Finset.disjoint_union_left.mpr
            ⟨heq ▸ hS it' (List.mem_cons_of_mem _ h), hpair.1 it' h⟩
        · simp only [heq, if_false]
          exact hS it' (List.mem_cons_of_mem _ h))
      (fun it' h => hdomD it' (List.mem_cons_of_mem _ h))
      (fun τ f hf => by
        by_cases heq : τ = it.1
        · simp only [heq, if_true, Finset.mem_union] at hf
          rcases hf with hf | hf
          · exact hdomS _ f hf
          · exact hdomD it (List.mem_cons_self ..) f hf
        · simp only [heq, if_false] at hf
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

/-- `step_node` as one flat fold over every `(tuple of rows, step output)` item. -/
theorem stepNode_eq_foldl (I : Traced Op Tau) (op : Op) (tables : List (Table Tau)) :
    stepNode I op tables =
      (tables.sections.flatMap (rowItems I op)).foldl (fun T it => unionInto T it.1 it.2) [] :=
  foldl_unionInto_flatMap (rowItems I op) tables.sections []

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
      rw [rowExpr, if_neg hne]
      exact rowExpr_of_mem hnd.2 h

theorem mem_of_rowExpr_ne :
    ∀ {T : Table Tau} {t : Tau}, rowExpr T t ≠ .empty → (t, rowExpr T t) ∈ T
  | [], _, h => absurd rfl h
  | (t', e') :: rows, t, h => by
    by_cases ht : t' = t
    · subst ht
      simp [rowExpr]
    · rw [rowExpr, if_neg ht] at h ⊢
      exact List.mem_cons_of_mem _ (mem_of_rowExpr_ne h)

theorem mem_map_fst_unionInto :
    ∀ (T : Table Tau) (tau : Tau) (e : Expr) {x : Tau},
      x ∈ (unionInto T tau e).map Prod.fst → x ∈ T.map Prod.fst ∨ x = tau
  | [], tau, e, x, h => by
    simp [unionInto] at h
    exact Or.inr h
  | (t, e') :: rows, tau, e, x, h => by
    by_cases ht : t = tau
    · rw [unionInto, if_pos ht] at h
      simp only [List.map_cons] at h ⊢
      exact Or.inl h
    · rw [unionInto, if_neg ht, List.map_cons, List.mem_cons] at h
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
    · rw [unionInto, if_pos ht, List.map_cons, List.nodup_cons]
      exact hnd
    · rw [unionInto, if_neg ht, List.map_cons, List.nodup_cons]
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

/-! ### Instances -/

/-- The specification side of an instance: what the construction denotes, what a trace is, and
    the obligations the paper leaves to each instance. -/
structure Instance (Op Tau : Type*) extends Traced Op Tau where
  /-- Partial candidates built at a node, each with the variables it owns. -/
  candidates : Node Op → Finset Assign
  /-- Trace of a partial candidate at a node. -/
  trace : Node Op → Assign → Tau
  /-- Variables the candidates of a node assign (`dom` in Definition 10). -/
  nodeDom : Node Op → Finset Var
  dom_eq : ∀ n, ∀ f ∈ candidates n, f.dom = nodeDom n
  /-- Variables an operation owns itself; the children's are pairwise disjoint and disjoint
      from them. -/
  owned : Op → Finset Var
  owned_disjoint : ∀ (op : Op) (cs : List (Node Op)), ∀ c ∈ cs, Disjoint (owned op) (nodeDom c)
  children_disjoint : ∀ op (cs : List (Node Op)), (cs.map nodeDom).Pairwise Disjoint
  /-- Every output of `step` assigns exactly the owned variables, each once. -/
  step_leaves : ∀ (op : Op) (taus : List Tau), ∀ out ∈ step op taus,
    (out.2.map Prod.fst).Nodup ∧ (out.2.map Prod.fst).toFinset = owned op
  /-- Distinct outputs assign the owned variables differently. -/
  step_nodup : ∀ (op : Op) (taus : List Tau),
    ((step op taus).map fun out => Assign.ofList out.2).Nodup
  /-- Obligation 3: the candidates at a node are the joins of one candidate per child with the
      leaves `step` yields for their traces, and `step` names their trace. -/
  cand_iff : ∀ (op : Op) (cs : List (Node Op)) (f : Assign), f ∈ candidates (.mk op cs) ↔
    ∃ fs : List Assign, List.Forall₂ (fun f c => f ∈ candidates c) fs cs ∧
      ∃ out ∈ step op (List.zipWith trace cs fs),
        f = (Assign.joinAll fs).join (Assign.ofList out.2)
  trace_mk : ∀ (op : Op) (cs : List (Node Op)) (fs : List Assign) (out : Tau × List (Var × Val)),
    List.Forall₂ (fun f c => f ∈ candidates c) fs cs →
    out ∈ step op (List.zipWith trace cs fs) →
    trace (.mk op cs) ((Assign.joinAll fs).join (Assign.ofList out.2)) = out.1
  /-- Obligation 2: solutionhood from the trace alone. -/
  solution : Node Op → Assign → Prop
  accept_iff : ∀ n f, f ∈ candidates n → (solution n f ↔ accept (trace n f) = true)

namespace Instance
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

theorem children_pairwise (op : Op) (cs : List (Node Op)) :
    cs.Pairwise fun c c' => Disjoint (I.nodeDom c) (I.nodeDom c') :=
  List.pairwise_map.mp (I.children_disjoint op cs)

/-- Restricting a join of one candidate per child to a child's variables recovers that
    candidate. -/
theorem restrict_foldl_join_cand :
    ∀ {fs : List Assign} {cs : List (Node Op)}, List.Forall₂ (fun f c => f ∈ I.candidates c) fs cs →
      cs.Pairwise (fun c c' => Disjoint (I.nodeDom c) (I.nodeDom c')) →
      ∀ e : Assign, (∀ c ∈ cs, Disjoint e.dom (I.nodeDom c)) →
      List.Forall₂ (fun f c => (fs.foldl Assign.join e).restrict (I.nodeDom c) = f) fs cs
  | [], [], _, _, _, _ => List.Forall₂.nil
  | f :: fs, c :: cs, hF, hpair, e, he => by
    rw [List.forall₂_cons] at hF
    rw [List.pairwise_cons] at hpair
    rw [List.foldl_cons]
    have hfd : f.dom = I.nodeDom c := I.dom_eq c f hF.1
    refine List.Forall₂.cons ?_ ?_
    · rw [Assign.restrict_foldl_join fs (e.join f)]
      · rw [Assign.restrict_join_of_disjoint_left (he c (List.mem_cons_self ..)).symm, ← hfd,
          Assign.restrict_dom_self]
      · intro g hg
        obtain ⟨c', hc', hgc'⟩ := forall₂_mem_left hF.2 hg
        rw [I.dom_eq c' g hgc']
        exact hpair.1 c' hc'
    · apply I.restrict_foldl_join_cand hF.2 hpair.2 (e.join f)
      intro c' hc'
      apply Finset.disjoint_of_subset_left (Assign.join_dom_subset e f)
      rw [Finset.disjoint_union_left]
      exact ⟨he c' (List.mem_cons_of_mem _ hc'), hfd ▸ hpair.1 c' hc'⟩

theorem restrict_joinAll {fs : List Assign} {cs : List (Node Op)}
    (hF : List.Forall₂ (fun f c => f ∈ I.candidates c) fs cs) (op : Op) :
    List.Forall₂ (fun f c => (Assign.joinAll fs).restrict (I.nodeDom c) = f) fs cs :=
  I.restrict_foldl_join_cand hF (I.children_pairwise op cs) Assign.empty
    (fun _ _ => by rw [Assign.empty_dom]; exact Finset.disjoint_empty_left _)

end Instance

/-- Claim 1 at the root: the DP's output denotes exactly the solution set. Not yet proved. -/
theorem solve_sound {Op Tau : Type*} [DecidableEq Tau] (I : Instance Op Tau) (n : Node Op) :
    Sem (I.toTraced.solve n) ((I.candidates n).filter fun f => I.accept (I.trace n f) = true) := by
  sorry

end Formalism
