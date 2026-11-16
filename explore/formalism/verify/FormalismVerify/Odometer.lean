import FormalismVerify.Spec

/-!
# The odometer of `scheme::step_node`

`step_node` visits one row from each child, every way, with an index vector it increments
from the end: the last digit first, a digit that overflows resets to `0` and carries, and the
loop is over when the carry comes out of the first digit. This file is the pure part of its
refinement: `incr` is that increment, `rest L idx` is the list of tuples still to visit from
`idx` (the current one first), and `rest_incr` says that visiting the current tuple and
incrementing walks `Traced.tuples` in order.
-/

namespace Formalism.Odometer
open Traced (tuples)

variable {α : Type*}

/-- The increment: radices first, digits second. The flag is the carry out of the first
    digit. -/
def incr : List ℕ → List ℕ → List ℕ × Bool
  | [], _ => ([], true)
  | _ :: _, [] => ([], true)
  | m :: ms, i :: is =>
    if (incr ms is).2 then
      if i + 1 < m then (i + 1 :: (incr ms is).1, false) else (0 :: (incr ms is).1, true)
    else (i :: (incr ms is).1, false)

/-- The tuples still to visit from a digit vector, the current one first. -/
def rest : List (List α) → List ℕ → List (List α)
  | [], _ => [[]]
  | _ :: _, [] => []
  | l :: L, i :: is =>
    match l.drop i with
    | [] => []
    | a :: l' => (rest L is).map (a :: ·) ++ l'.flatMap fun b => (tuples L).map (b :: ·)

/-- A digit vector addresses a row in every table. -/
def Valid (L : List (List α)) (idx : List ℕ) : Prop :=
  List.Forall₂ (fun i (l : List α) => i < l.length) idx L

theorem Valid.ne_nil : ∀ {L : List (List α)} {idx : List ℕ}, Valid L idx → ∀ l ∈ L, l ≠ []
  | [], _, _ => by simp
  | _ :: _, [], h => by cases h
  | l :: L, i :: is, h => by
    rw [Valid, List.forall₂_cons] at h
    intro l' hl'
    rw [List.mem_cons] at hl'
    rcases hl' with rfl | hl'
    · exact List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h.1)
    · exact Valid.ne_nil h.2 l' hl'

theorem Valid.length_eq {L : List (List α)} {idx : List ℕ} (h : Valid L idx) :
    idx.length = L.length :=
  List.Forall₂.length_eq h

theorem valid_zeros : ∀ L : List (List α), (∀ l ∈ L, l ≠ []) → Valid L (List.replicate L.length 0)
  | [], _ => List.Forall₂.nil
  | l :: L, h => by
    rw [List.length_cons, List.replicate_succ]
    refine List.Forall₂.cons ?_ (valid_zeros L fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    exact List.length_pos_iff.mpr (h l (List.mem_cons_self ..))

theorem rest_zeros : ∀ L : List (List α), (∀ l ∈ L, l ≠ []) →
    rest L (List.replicate L.length 0) = tuples L
  | [], _ => by simp [rest, tuples]
  | l :: L, h => by
    obtain ⟨a, l', rfl⟩ : ∃ a l', l = a :: l' := by
      cases l with
      | nil => exact absurd rfl (h [] (List.mem_cons_self ..))
      | cons a l' => exact ⟨a, l', rfl⟩
    rw [List.length_cons, List.replicate_succ]
    simp only [rest, List.drop_zero, rest_zeros L fun l hl => h l (List.mem_cons_of_mem _ hl),
      tuples, List.flatMap_cons]

theorem incr_length : ∀ (ms is : List ℕ), is.length = ms.length →
    (incr ms is).1.length = ms.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | m :: ms, i :: is, h => by
    have ih := incr_length ms is (by simpa using h)
    rcases hinc : incr ms is with ⟨is', c⟩
    simp only [hinc] at ih
    simp only [incr, hinc]
    cases c
    · simp [ih]
    · rw [ite_eq_left rfl]
      split <;> simp [ih]

theorem incr_carry : ∀ (ms is : List ℕ), is.length = ms.length → (incr ms is).2 = true →
    (incr ms is).1 = List.replicate ms.length 0
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | m :: ms, i :: is, h, hc => by
    have ih := incr_carry ms is (by simpa using h)
    rcases hinc : incr ms is with ⟨is', c⟩
    simp only [hinc] at ih
    simp only [incr, hinc] at hc ⊢
    cases c
    · simp at hc
    · rw [ite_eq_left rfl] at hc ⊢
      rw [List.length_cons, List.replicate_succ]
      split
      · rename_i hlt
        rw [ite_eq_left hlt] at hc
        simp at hc
      · simp [ih rfl]

/-- One step of the odometer walks `tuples` in order: the current tuple is `cur`, the row at
    each digit; then either every digit wrapped and `cur` was the last tuple, or the next
    digit vector is valid and the rest continues with it. -/
theorem rest_incr : ∀ (L : List (List α)) (idx : List ℕ), Valid L idx →
    ∃ cur : List α,
      List.Forall₂ (fun (r : α) (p : List α × ℕ) => p.1[p.2]? = some r) cur (L.zip idx) ∧
      (if (incr (L.map List.length) idx).2 then rest L idx = [cur]
        else rest L idx = cur :: rest L (incr (L.map List.length) idx).1 ∧
          Valid L (incr (L.map List.length) idx).1)
  | [], [], _ => ⟨[], List.Forall₂.nil, by simp [rest, incr]⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | l :: L, i :: is, h => by
    rw [Valid, List.forall₂_cons] at h
    obtain ⟨hi, his⟩ := h
    obtain ⟨cur', hcur', hrest'⟩ := rest_incr L is his
    have hdrop : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hlen : is.length = (L.map List.length).length := by
      rw [List.length_map]
      exact his.length_eq
    refine ⟨l[i] :: cur', ?_, ?_⟩
    · rw [List.zip_cons_cons]
      exact List.Forall₂.cons (List.getElem?_eq_getElem hi) hcur'
    · rcases hinc : incr (L.map List.length) is with ⟨is', c⟩
      simp only [hinc] at hrest'
      simp only [List.map_cons, incr, hinc]
      cases c
      · -- the rest did not wrap: this digit stays
        rw [ite_eq_right Bool.false_ne_true] at hrest' ⊢
        obtain ⟨hrest', hvalid'⟩ := hrest'
        show rest (l :: L) (i :: is) = (l[i] :: cur') :: rest (l :: L) (i :: is') ∧
          Valid (l :: L) (i :: is')
        refine ⟨?_, List.Forall₂.cons hi hvalid'⟩
        simp only [rest, hdrop, hrest', List.map_cons, List.cons_append]
      · -- the rest wrapped: `is` was its last tuple, and restarts at zeros
        rw [ite_eq_left rfl] at hrest' ⊢
        have hzeros : is' = List.replicate L.length 0 := by
          have := incr_carry (L.map List.length) is hlen (by simp [hinc])
          rw [hinc, List.length_map] at this
          exact this
        have hne : ∀ l' ∈ L, l' ≠ [] := his.ne_nil
        by_cases hlt : i + 1 < l.length
        · -- this digit can still advance: the rest restarts in full
          rw [ite_eq_left hlt]
          show rest (l :: L) (i :: is) = (l[i] :: cur') :: rest (l :: L) ((i + 1) :: is') ∧
            Valid (l :: L) ((i + 1) :: is')
          have hdrop1 : l.drop (i + 1) = l[i + 1] :: l.drop (i + 1 + 1) :=
            List.drop_eq_getElem_cons hlt
          refine ⟨?_, List.Forall₂.cons hlt (by rw [hzeros]; exact valid_zeros L hne)⟩
          simp only [rest, hdrop, hdrop1, hrest', hzeros, rest_zeros L hne, List.map_cons,
            List.map_nil, List.flatMap_cons, List.singleton_append]
        · -- this digit wraps too: `cur` was the last tuple
          rw [ite_eq_right hlt]
          show rest (l :: L) (i :: is) = [l[i] :: cur']
          have hnil : l.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
          simp only [rest, hdrop, hrest', hnil, List.map_cons, List.map_nil, List.flatMap_nil,
            List.append_nil]

theorem flatMap_nil_fun {β γ : Type*} : ∀ l : List β, (l.flatMap fun _ => ([] : List γ)) = []
  | [] => rfl
  | _ :: l => by rw [List.flatMap_cons, List.nil_append, flatMap_nil_fun l]

theorem tuples_eq_nil : ∀ L : List (List α), (∃ l ∈ L, l = []) → tuples L = []
  | [], h => by simp at h
  | l :: L, h => by
    simp only [List.mem_cons, exists_eq_or_imp] at h
    rcases h with rfl | h
    · simp [tuples]
    · simp [tuples, tuples_eq_nil L h, flatMap_nil_fun]

/-! ### Table lengths under `unionInto` -/

section Length
variable {Tau : Type*} [DecidableEq Tau]

theorem length_le_unionInto (tau : Tau) (e : Expr) :
    ∀ T : List (Tau × Expr), T.length ≤ (Traced.unionInto T tau e).length
  | [] => by simp [Traced.unionInto]
  | (t, e') :: rows => by
    rw [Traced.unionInto]
    split
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (length_le_unionInto tau e rows)

theorem length_le_foldl_unionInto :
    ∀ (items : List (Tau × Expr)) (T : List (Tau × Expr)),
      T.length ≤ (items.foldl (fun T it => Traced.unionInto T it.1 it.2) T).length
  | [], T => le_rfl
  | it :: items, T => by
    rw [List.foldl_cons]
    exact (length_le_unionInto it.1 it.2 T).trans (length_le_foldl_unionInto items _)

end Length

end Formalism.Odometer
