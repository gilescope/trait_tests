import Mathlib

/-!
# Quicksort, as `hylo::sort::quicksort` computes it

`quicksort = hylo_node_tree(Pivot, Concat)`: `Pivot::unfold` pops the pivot off the back of
the vector, then pops the rest off the back, each to the left if it is below the pivot and to
the right otherwise; `Concat::fold` is left, pivot, right. So the Rust sorts a vector by
recursing on its *reverse*: `qs (p :: rest)` partitions `rest` around `p`. `quicksort v` is
`qs v.reverse`, and the two theorems are the usual ones: the output is a permutation of the
input, and it is sorted.
-/

namespace Formalism.Quicksort
variable {α : Type*} [LinearOrder α]

/-- Quicksort on a list read front to back: the head is the pivot. -/
def qs : List α → List α
  | [] => []
  | p :: rest =>
    qs (rest.filter fun x => decide (x < p)) ++ p :: qs (rest.filter fun x => !decide (x < p))
termination_by l => l.length
decreasing_by
  all_goals
    simp_wf
    all_goals try simp only [List.length_cons] at *
    all_goals
      have h1 := List.length_filter_le (fun x => decide (x < p)) rest
      have h2 := List.length_filter_le (fun x => !decide (x < p)) rest
      omega

/-- The Rust pops from the back, so it runs `qs` on the reverse. -/
def quicksort (v : List α) : List α := qs v.reverse

theorem qs_perm (l : List α) : (qs l).Perm l := by
  induction l using qs.induct with
  | case1 => simp [qs]
  | case2 p rest ih1 ih2 =>
    rw [qs]
    exact ((ih1.append (ih2.cons p)).trans List.perm_middle).trans
      ((List.filter_append_perm _ rest).cons p)

theorem qs_sorted (l : List α) : (qs l).Pairwise (· ≤ ·) := by
  induction l using qs.induct with
  | case1 => simp [qs]
  | case2 p rest ih1 ih2 =>
    rw [qs, List.pairwise_append]
    refine ⟨ih1, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, ih2⟩
      intro b hb
      rw [(qs_perm _).mem_iff, List.mem_filter] at hb
      have hb' : ¬ b < p := by simpa using hb.2
      exact not_lt.mp hb'
    · intro a ha b hb
      rw [(qs_perm _).mem_iff, List.mem_filter] at ha
      have ha' : a < p := by simpa using ha.2
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ha'.le
      · rw [(qs_perm _).mem_iff, List.mem_filter] at hb
        have hb' : ¬ b < p := by simpa using hb.2
        exact ha'.le.trans (not_lt.mp hb')

theorem quicksort_perm (v : List α) : (quicksort v).Perm v :=
  (qs_perm _).trans (List.reverse_perm v)

theorem quicksort_sorted (v : List α) : (quicksort v).Pairwise (· ≤ ·) :=
  qs_sorted _

theorem quicksort_length (v : List α) : (quicksort v).length = v.length :=
  (quicksort_perm v).length_eq

/-- `qs` on elements compared through `R`: what the Rust does with `Ord` on `T`. -/
def qsBy {β : Type*} (R : β → α) : List β → List β
  | [] => []
  | p :: rest =>
    qsBy R (rest.filter fun x => decide (R x < R p)) ++
      p :: qsBy R (rest.filter fun x => !decide (R x < R p))
termination_by l => l.length
decreasing_by
  all_goals
    simp_wf
    all_goals try simp only [List.length_cons] at *
    all_goals
      have h1 := List.length_filter_le (fun x => decide (R x < R p)) rest
      have h2 := List.length_filter_le (fun x => !decide (R x < R p)) rest
      omega

/-- Sorting through an injective reading of the elements is sorting the readings. -/
theorem qs_map {β : Type*} (R : β → α) (l : List β) : qs (l.map R) = (qsBy R l).map R := by
  induction l using qsBy.induct R with
  | case1 => simp [qs, qsBy]
  | case2 p rest ih1 ih2 =>
    rw [List.map_cons, qs, qsBy, List.map_append, List.map_cons]
    simp only [List.filter_map, Function.comp_def]
    rw [← ih1, ← ih2]

/-- `quicksort` through `R`. -/
def quicksortBy {β : Type*} (R : β → α) (v : List β) : List β := qsBy R v.reverse

theorem quicksortBy_map {β : Type*} (R : β → α) (v : List β) :
    quicksort (v.map R) = (quicksortBy R v).map R := by
  rw [quicksort, quicksortBy, ← List.map_reverse, qs_map]

end Formalism.Quicksort
