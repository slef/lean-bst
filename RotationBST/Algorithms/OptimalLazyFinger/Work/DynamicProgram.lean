module

public import RotationBST.Algorithms.OptimalLazyFinger.Work.Preprocessing
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.OptimalLazyFinger.Work
open Cslib.Algorithms.Lean

@[simp] theorem minimum_time (initial : Entry) (xs : List Entry) :
    (minimum initial xs).time = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [minimum, ih]; omega

theorem candidate_time (w : Nat → Nat → Computation Nat) (previous : Array (Array Entry))
    (n lo k C : Nat) (hw : ∀ a b, (w a b).time ≤ C) :
    (candidate w previous n lo k).time ≤ C + 12 := by
  have h := hw lo (lo + n + 1)
  simpa only [candidate, TimeM.time_bind, charge_time] using Nat.add_le_add_right h 12

/-- The initial candidate and all candidate-list entries are counted; in
particular the implementation's repeated root-zero candidate is not omitted. -/
theorem cell_time (w : Nat → Nat → Computation Nat) (previous : Array (Array Entry))
    (N n lo C : Nat) (hw : ∀ a b, (w a b).time ≤ C) :
    (cell w previous N n lo).time ≤ (n + 2) * (C + 16) + 2 := by
  have first := candidate_time w previous n lo 0 C hw
  have choices := mapList_time_le
    (fun k : Fin (n + 1) => candidate w previous n lo k.val)
    (List.finRange (n + 1)) (C + 12) (by intro k _; exact candidate_time w previous n lo k.val C hw)
  simp only [List.length_finRange] at choices
  by_cases h : lo + n + 1 ≤ N
  · simp only [cell, TimeM.time_bind, charge_time, charge_ret, h, decide_true, ↓reduceIte,
      minimum_time, mapList_ret, List.length_map, List.length_finRange]
    nlinarith
  · simp [cell, h]
    nlinarith

/-- A quadratic number of table cells, each scanning at most linearly many
roots. The cost of a toll query is supplied explicitly by `C`. -/
theorem tabulate_time (w : Nat → Nat → Computation Nat) (N stages C : Nat)
    (hw : ∀ a b, (w a b).time ≤ C) (hs : stages ≤ N) :
    (tabulate w N stages).time ≤
      N + 3 + stages * ((N + 1) ^ 2 * (C + 16) + 5 * (N + 1) + 5) := by
  induction stages with
  | zero => simp [tabulate]
  | succ stages ih =>
    have old := ih (by omega)
    have rowBound := arrayOfFn_time_le (N + 1)
      (fun lo : Fin (N + 1) => cell w (tabulate w N stages).ret N stages lo.val)
      ((N + 1) * (C + 16) + 2) (by
        intro lo
        have h := cell_time w (tabulate w N stages).ret N stages lo.val C hw
        have hm := Nat.mul_le_mul_right (C + 16) (show stages + 2 ≤ N + 1 by omega)
        omega)
    simp only [tabulate, TimeM.time_bind, charge_time]
    nlinarith

theorem optimize_time (w : Nat → Nat → Computation Nat) (n C : Nat)
    (hw : ∀ a b, (w a b).time ≤ C) :
    (optimize w n).time ≤ n + 5 + n * ((n + 1) ^ 2 * (C + 16) + 5 * (n + 1) + 5) := by
  have h := tabulate_time w n n C hw le_rfl
  simp only [optimize, TimeM.time_bind, charge_time]
  omega

/-- End-to-end bound in the explicit unit-cost RAM model, including all
preprocessing. The harmless `n+1` handles initialization and the empty universe. -/
theorem treeFrom_time (n p : Nat) (xs : List Nat) :
    (treeFrom n p xs).time ≤ 4 * xs.length + 64 * (n + 1) ^ 3 := by
  have hp := prepare_time (n + 1) p xs
  have ho := optimize_time (toll (prepare (n + 1) p xs).ret (n + 1)) n 47
    (by intro a b; rw [toll_time])
  simp only [treeFrom, TimeM.time_bind, TimeM.time_pure, Nat.add_zero]
  nlinarith [Nat.zero_le (n ^ 3)]

theorem tree_time (n : Nat) (xs : List Nat) :
    (tree n xs).time ≤ 4 * xs.length + 64 * (n + 1) ^ 3 := treeFrom_time n n xs

/-- On a nonempty universe, the bound has the usual `m + n³` form. -/
theorem treeFrom_time_nonempty (n p : Nat) (xs : List Nat) (hn : 0 < n) :
    (treeFrom n p xs).time ≤ 4 * xs.length + 512 * n ^ 3 := by
  have h := treeFrom_time n p xs
  have hp : (n + 1) ^ 3 ≤ (2 * n) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  nlinarith

end RotationBST.OptimalLazyFinger.Work
