module

public import RotationBST.WorkingSet.Distinct
public import RotationBST.WorkingSet.LogBound
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Count

@[expose] public section

namespace RotationBST.Bounds

/-- Number of requests since the previous occurrence, or the length of the
history when the key has not yet occurred. -/
def age (past : List Nat) (x : Nat) : Nat := (past.reverse.takeWhile (· != x)).length

def nextAge (ages : Nat → Nat) (x : Nat) : Nat → Nat :=
  fun y => if y = x then 0 else ages y + 1

/-- Positive time gaps between consecutive occurrences of one key; the initial
age permits this to be used on a suffix of a request sequence. -/
def gaps (x : Nat) (a : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if y = x then (a + 1) :: gaps x 0 ys else gaps x (a + 1) ys

noncomputable def gapSum (ages : Nat → Nat) : List Nat → ℝ
  | [] => 0
  | x :: xs => Real.logb 2 (ages x + 1 : Nat) + gapSum (nextAge ages x) xs

/-- Count first occurrences relative to the supplied history. -/
def newCount (past : List Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if x ∈ past then 0 else 1) + newCount (past ++ [x]) xs

theorem age_step (past : List Nat) (x : Nat) : age (past ++ [x]) = nextAge (age past) x := by
  funext y
  by_cases h : y = x
  · subst y; simp [age, nextAge]
  · have h' : x ≠ y := Ne.symm h
    simp [age, nextAge, h, h']

theorem gaps_length (x a : Nat) (xs : List Nat) : (gaps x a xs).length = xs.count x := by
  induction xs generalizing a with
  | nil => simp [gaps]
  | cons y ys ih => by_cases h : y = x <;> simp [gaps, h, ih]

theorem gaps_pos (x a : Nat) (xs : List Nat) : ∀ g ∈ gaps x a xs, 0 < g := by
  induction xs generalizing a with
  | nil => simp [gaps]
  | cons y ys ih =>
      by_cases h : y = x
      · simp only [gaps, ite_eq_left h, List.mem_cons]
        intro g hg
        rcases hg with rfl | hg
        · omega
        · exact ih 0 g hg
      · simp only [gaps, ite_eq_right h]
        exact ih (a + 1)

theorem gaps_sum_le (x a : Nat) (xs : List Nat) : (gaps x a xs).sum ≤ a + xs.length := by
  induction xs generalizing a with
  | nil => simp [gaps]
  | cons y ys ih =>
      by_cases h : y = x
      · have := ih 0
        simp only [gaps, ite_eq_left h, List.sum_cons, List.length_cons]
        omega
      · have := ih (a + 1)
        simp only [gaps, ite_eq_right h, List.length_cons]
        omega

theorem eraseDups_length_le (xs : List Nat) : xs.eraseDups.length ≤ xs.length := by
  cases xs with
  | nil => simp
  | cons x xs =>
      rw [List.eraseDups_cons, List.length_cons, List.length_cons]
      have h := eraseDups_length_le (xs.filter fun y => !y == x)
      have hf := List.length_filter_le (fun y => !y == x) xs
      omega
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

theorem workingSet_charge (n : Nat) (past : List Nat) (x : Nat) :
    (1 + (workingSetNumber n past x).log2 : Nat) ≤
      (1 : ℝ) + Real.logb 2 (age past x + 1 : Nat) +
        if x ∈ past then 0 else Real.logb 2 n := by
  have hg : (1 : ℝ) ≤ (age past x + 1 : Nat) := by exact_mod_cast Nat.le_add_left 1 (age past x)
  have hglog := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hg
  simp only [Nat.cast_add, Nat.cast_one] at hglog
  by_cases hx : x ∈ past
  · have hlen := eraseDups_length_le (past.reverse.takeWhile (· != x))
    have hle : workingSetNumber n past x ≤ age past x + 1 := by
      simp only [workingSetNumber, ite_eq_left hx, age]; omega
    have hn := Real.log2_le_logb (workingSetNumber n past x)
    have hp : 0 < (workingSetNumber n past x : ℝ) := by
      simp only [workingSetNumber, ite_eq_left hx, Nat.cast_add, Nat.cast_one]
      positivity
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp
      (show (workingSetNumber n past x : ℝ) ≤ (age past x + 1 : Nat) by exact_mod_cast hle)
    simp only [Nat.cast_add, Nat.cast_one] at hlog
    simp only [ite_eq_left hx, Nat.cast_add, Nat.cast_one]
    linarith
  · have hn := Real.log2_le_logb n
    simp only [workingSetNumber, ite_eq_right hx, Nat.cast_add, Nat.cast_one]
    linarith

theorem workingSet_le_gaps (n : Nat) (past xs : List Nat) :
    (workingSetSum n past xs : ℝ) ≤ (xs.length : ℝ) +
      (newCount past xs : ℝ) * Real.logb 2 n + gapSum (age past) xs := by
  induction xs generalizing past with
  | nil => simp [workingSetSum, newCount, gapSum]
  | cons x xs ih =>
      have hi := ih (past ++ [x])
      rw [age_step] at hi
      have hc := workingSet_charge n past x
      by_cases hx : x ∈ past
      · simp only [workingSetSum, newCount, gapSum, List.length_cons,
          ite_eq_left hx, zero_add, Nat.cast_add, Nat.cast_one] at hc ⊢
        linarith
      · simp only [workingSetSum, newCount, gapSum, List.length_cons,
          ite_eq_right hx, Nat.cast_add, Nat.cast_one] at hc ⊢
        nlinarith

theorem newCount_card (past xs : List Nat) :
    newCount past xs + past.toFinset.card = (past ++ xs).toFinset.card := by
  induction xs generalizing past with
  | nil => simp [newCount]
  | cons x xs ih =>
      have hi := ih (past ++ [x])
      simp only [List.append_assoc, List.singleton_append] at hi
      by_cases hx : x ∈ past
      · have hi' : (past ++ [x]).toFinset = past.toFinset := by
          ext y; simp only [List.mem_toFinset, List.mem_append, List.mem_singleton]
          constructor
          · intro h; rcases h with h | rfl; exact h; exact hx
          · exact Or.inl
        simp only [newCount, ite_eq_left hx, zero_add, hi'] at *
        exact hi
      · have hi' : (past ++ [x]).toFinset.card = past.toFinset.card + 1 := by
          rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
            Finset.insert_empty, Finset.union_singleton]
          exact Finset.card_insert_of_notMem (by simpa using hx)
        simp only [newCount, ite_eq_right hx]
        rw [hi'] at hi
        omega

theorem newCount_le (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    newCount [] xs ≤ n := by
  have h := newCount_card [] xs
  simp only [List.toFinset_nil, Finset.card_empty, Nat.add_zero, List.nil_append] at h
  rw [h]
  have hs : xs.toFinset ⊆ Finset.range n := by
    intro x hx; exact Finset.mem_range.mpr (valid x (List.mem_toFinset.mp hx))
  simpa using Finset.card_le_card hs

end RotationBST.Bounds
