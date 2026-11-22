import Mathlib

/-!
# Quicksort, as `hylo::sort::quicksort` computes it

`quicksort = hylo_node_tree(Pivot, Concat)`: `Pivot::unfold` pops the pivot off the back of
the vector, then pops the rest off the back, each to the left if it is below the pivot and to
the right otherwise; `Concat::fold` is left, pivot, right. So the Rust reads a vector from the
back: `qs (p :: rest)` partitions `rest` around `p`, and each partition is a vector read from
the back again, so the recursive calls are on the *reverses* of the partitions. `quicksort v`
is `qs v.reverse`. The theorems are the usual ones: the output is a permutation of the input,
and it is sorted. `qsBy R` is the same on elements compared through a reading `R`, which is
what the Rust does with `Ord` on `T`; `qs_map` says it sorts the readings.

The recursion is written with a fuel that bounds the length (structurally), which keeps the
equations plain: well-founded recursion through `filter` would be rewritten by Lean to recurse
on attached lists.
-/

namespace Formalism.Quicksort
variable {α : Type*} [LinearOrder α]

/-- `qsF n l`: quicksort with fuel `n ≥ l.length`. The head is the pivot; the partitions are
    read from the back. -/
def qsF : ℕ → List α → List α
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, p :: rest =>
    qsF n (rest.filter fun x => decide (x < p)).reverse ++
      p :: qsF n (rest.filter fun x => !decide (x < p)).reverse

/-- Quicksort on a list read front to back. -/
def qs (l : List α) : List α := qsF l.length l

/-- The Rust pops from the back, so it runs `qs` on the reverse. -/
def quicksort (v : List α) : List α := qs v.reverse

theorem length_filter_reverse_le (q : α → Bool) (rest : List α) :
    (rest.filter q).reverse.length ≤ rest.length := by
  rw [List.length_reverse]
  exact List.length_filter_le q rest

theorem qsF_eq_of_le : ∀ (n m : ℕ) (l : List α), l.length ≤ n → l.length ≤ m →
    qsF n l = qsF m l
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, l, hn, _ => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hn), qsF, qsF]
  | _ + 1, 0, l, _, hm => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hm), qsF, qsF]
  | _ + 1, _ + 1, [], _, _ => by rw [qsF, qsF]
  | n + 1, m + 1, p :: rest, hn, hm => by
    rw [List.length_cons] at hn hm
    rw [qsF, qsF,
      qsF_eq_of_le n m _ ((length_filter_reverse_le _ rest).trans (by omega))
        ((length_filter_reverse_le _ rest).trans (by omega)),
      qsF_eq_of_le n m _ ((length_filter_reverse_le _ rest).trans (by omega))
        ((length_filter_reverse_le _ rest).trans (by omega))]

theorem qs_nil : qs ([] : List α) = [] := rfl

theorem qs_cons (p : α) (rest : List α) :
    qs (p :: rest) = qs (rest.filter fun x => decide (x < p)).reverse ++
      p :: qs (rest.filter fun x => !decide (x < p)).reverse := by
  unfold qs
  rw [List.length_cons, qsF,
    qsF_eq_of_le rest.length _ _ (length_filter_reverse_le _ rest) le_rfl,
    qsF_eq_of_le rest.length _ _ (length_filter_reverse_le _ rest) le_rfl]

theorem qsF_perm : ∀ (n : ℕ) (l : List α), l.length ≤ n → (qsF n l).Perm l
  | 0, l, h => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h), qsF]
  | _ + 1, [], _ => by rw [qsF]
  | n + 1, p :: rest, h => by
    rw [List.length_cons] at h
    rw [qsF]
    have h1 := (qsF_perm n _ ((length_filter_reverse_le _ rest).trans (by omega))).trans
      (List.reverse_perm _)
    have h2 := (qsF_perm n _ ((length_filter_reverse_le _ rest).trans (by omega))).trans
      (List.reverse_perm _)
    exact ((h1.append (h2.cons p)).trans List.perm_middle).trans
      ((List.filter_append_perm _ rest).cons p)

theorem qsF_sorted : ∀ (n : ℕ) (l : List α), l.length ≤ n → (qsF n l).Pairwise (· ≤ ·)
  | 0, l, h => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h), qsF]
    exact List.Pairwise.nil
  | _ + 1, [], _ => by
    rw [qsF]
    exact List.Pairwise.nil
  | n + 1, p :: rest, h => by
    rw [List.length_cons] at h
    have hl1 := (length_filter_reverse_le (fun x => decide (x < p)) rest).trans
      (Nat.le_of_lt_succ (Nat.lt_succ_of_le (by omega)) : rest.length ≤ n)
    have hl2 := (length_filter_reverse_le (fun x => !decide (x < p)) rest).trans
      (Nat.le_of_lt_succ (Nat.lt_succ_of_le (by omega)) : rest.length ≤ n)
    rw [qsF, List.pairwise_append]
    refine ⟨qsF_sorted n _ hl1, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, qsF_sorted n _ hl2⟩
      intro b hb
      rw [(qsF_perm n _ hl2).mem_iff, List.mem_reverse, List.mem_filter] at hb
      have hb' : ¬ b < p := by simpa using hb.2
      exact not_lt.mp hb'
    · intro a ha b hb
      rw [(qsF_perm n _ hl1).mem_iff, List.mem_reverse, List.mem_filter] at ha
      have ha' : a < p := by simpa using ha.2
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ha'.le
      · rw [(qsF_perm n _ hl2).mem_iff, List.mem_reverse, List.mem_filter] at hb
        have hb' : ¬ b < p := by simpa using hb.2
        exact ha'.le.trans (not_lt.mp hb')

theorem qs_perm (l : List α) : (qs l).Perm l := qsF_perm l.length l le_rfl

theorem qs_sorted (l : List α) : (qs l).Pairwise (· ≤ ·) := qsF_sorted l.length l le_rfl

theorem quicksort_perm (v : List α) : (quicksort v).Perm v :=
  (qs_perm _).trans (List.reverse_perm v)

theorem quicksort_sorted (v : List α) : (quicksort v).Pairwise (· ≤ ·) :=
  qs_sorted _

theorem quicksort_length (v : List α) : (quicksort v).length = v.length :=
  (quicksort_perm v).length_eq

/-! ## Through a reading of the elements -/

variable {β : Type*}

/-- `qsF` on elements compared through `R`: what the Rust does with `Ord` on `T`. -/
def qsByF (R : β → α) : ℕ → List β → List β
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, p :: rest =>
    qsByF R n (rest.filter fun x => decide (R x < R p)).reverse ++
      p :: qsByF R n (rest.filter fun x => !decide (R x < R p)).reverse

def qsBy (R : β → α) (l : List β) : List β := qsByF R l.length l

/-- `quicksort` through `R`. -/
def quicksortBy (R : β → α) (v : List β) : List β := qsBy R v.reverse

theorem length_filter_reverse_le' (q : β → Bool) (rest : List β) :
    (rest.filter q).reverse.length ≤ rest.length := by
  rw [List.length_reverse]
  exact List.length_filter_le q rest

theorem qsByF_eq_of_le (R : β → α) : ∀ (n m : ℕ) (l : List β), l.length ≤ n → l.length ≤ m →
    qsByF R n l = qsByF R m l
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, l, hn, _ => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hn), qsByF, qsByF]
  | _ + 1, 0, l, _, hm => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hm), qsByF, qsByF]
  | _ + 1, _ + 1, [], _, _ => by rw [qsByF, qsByF]
  | n + 1, m + 1, p :: rest, hn, hm => by
    rw [List.length_cons] at hn hm
    rw [qsByF, qsByF,
      qsByF_eq_of_le R n m _ ((length_filter_reverse_le' _ rest).trans (by omega))
        ((length_filter_reverse_le' _ rest).trans (by omega)),
      qsByF_eq_of_le R n m _ ((length_filter_reverse_le' _ rest).trans (by omega))
        ((length_filter_reverse_le' _ rest).trans (by omega))]

theorem qsBy_nil (R : β → α) : qsBy R [] = [] := rfl

theorem qsBy_cons (R : β → α) (p : β) (rest : List β) :
    qsBy R (p :: rest) = qsBy R (rest.filter fun x => decide (R x < R p)).reverse ++
      p :: qsBy R (rest.filter fun x => !decide (R x < R p)).reverse := by
  unfold qsBy
  rw [List.length_cons, qsByF,
    qsByF_eq_of_le R rest.length _ _ (length_filter_reverse_le' _ rest) le_rfl,
    qsByF_eq_of_le R rest.length _ _ (length_filter_reverse_le' _ rest) le_rfl]

/-- Sorting through a reading of the elements sorts the readings. -/
theorem qsF_map (R : β → α) : ∀ (n : ℕ) (l : List β), qsF n (l.map R) = (qsByF R n l).map R
  | 0, _ => by rw [qsF, qsByF, List.map_nil]
  | _ + 1, [] => by rw [List.map_nil, qsF, qsByF, List.map_nil]
  | n + 1, p :: rest => by
    rw [List.map_cons, qsF, qsByF, List.map_append, List.map_cons, List.filter_map, List.filter_map,
      ← List.map_reverse, ← List.map_reverse, qsF_map R n, qsF_map R n]
    rfl

theorem qs_map (R : β → α) (l : List β) : qs (l.map R) = (qsBy R l).map R := by
  unfold qs qsBy
  rw [List.length_map, qsF_map]

theorem quicksortBy_map (R : β → α) (v : List β) :
    quicksort (v.map R) = (quicksortBy R v).map R := by
  rw [quicksort, quicksortBy, ← List.map_reverse, qs_map]

theorem qsByF_perm (R : β → α) : ∀ (n : ℕ) (l : List β), l.length ≤ n → (qsByF R n l).Perm l
  | 0, l, h => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h), qsByF]
  | _ + 1, [], _ => by rw [qsByF]
  | n + 1, p :: rest, h => by
    rw [List.length_cons] at h
    rw [qsByF]
    have h1 := (qsByF_perm R n _ ((length_filter_reverse_le' _ rest).trans (by omega))).trans
      (List.reverse_perm _)
    have h2 := (qsByF_perm R n _ ((length_filter_reverse_le' _ rest).trans (by omega))).trans
      (List.reverse_perm _)
    exact ((h1.append (h2.cons p)).trans List.perm_middle).trans
      ((List.filter_append_perm _ rest).cons p)

theorem qsBy_perm (R : β → α) (l : List β) : (qsBy R l).Perm l := qsByF_perm R l.length l le_rfl

theorem quicksortBy_perm (R : β → α) (v : List β) : (quicksortBy R v).Perm v :=
  (qsBy_perm R _).trans (List.reverse_perm v)

theorem quicksortBy_length (R : β → α) (v : List β) : (quicksortBy R v).length = v.length :=
  (quicksortBy_perm R v).length_eq

end Formalism.Quicksort
