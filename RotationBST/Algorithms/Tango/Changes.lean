module

public import RotationBST.Bounds.Interleave.Basic
public import RotationBST.Algorithms.Tango.Definitions.Abstract

@[expose] public section
namespace RotationBST.Tango
open Wilber

theorem interleave_step (t : Tree) (past : List Nat) (x : Nat) (valid : x < t.size) :
    interleave t (past ++ [x]) = interleave t past + changes t past x := by
  induction t generalizing past x with
  | nil => simp [Tree.size] at valid
  | node l r il ir =>
    have hv : x < l.size + 1 + r.size := valid
    simp only [interleave, changes, ite_eq_left hv, regions_append, left_append, right_append]
    have region : regions l.size (l.size + 1 + r.size) [x] = [decide (x ≤ l.size)] := by
      simp [regions, hv]
    rw [region, alternations_append]
    by_cases hl : x < l.size
    · have hr : ¬ l.size < x := by omega
      simp only [leftRequests, rightRequests, List.filter_cons, decide_eq_true_eq,
        hl, hr, ↓reduceIte, List.filter_nil, List.map_nil, List.append_nil,
        ]
      have hrec := il (leftRequests l.size past) x hl
      simp only [leftRequests] at hrec
      omega
    · by_cases he : x = l.size
      · subst x
        simp [leftRequests, rightRequests, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · have hr : l.size < x := by omega
        have hv' : x - l.size - 1 < r.size := by omega
        simp only [leftRequests, rightRequests, List.filter_cons, decide_eq_true_eq,
          hl, hr, ↓reduceIte, List.filter_nil, List.map_nil, List.append_nil,
          List.map_cons, ite_eq_right he]
        have hrec := ir (rightRequests l.size past) (x - l.size - 1) hv'
        simp only [rightRequests] at hrec
        omega

theorem changeCost_eq (t : Tree) (past xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    interleave t (past ++ xs) = interleave t past + changeCost t past xs := by
  induction xs generalizing past with
  | nil => simp [changeCost]
  | cons x xs ih =>
    have hx := interleave_step t past x (valid x (List.mem_cons_self ..))
    have h := ih (past ++ [x]) (fun y hy => valid y (List.mem_cons_of_mem _ hy))
    simpa [changeCost, List.append_assoc, hx, Nat.add_assoc] using h

theorem downward_length {t : Tree} {path : List Bool} (h : DownwardPath t path) :
    path.length + 1 ≤ height t := by
  induction h with
  | stop l r => simp [height]
  | left _ ih => simp only [List.length_cons, height]; omega
  | right _ ih => simp only [List.length_cons, height]; omega

theorem changes_le_height (t : Tree) (past : List Nat) (x : Nat) :
    changes t past x ≤ height t := by
  induction t generalizing past x with
  | nil => simp [changes, height]
  | node l r il ir =>
    have hs := switch_le_one (regions l.size (l.size + 1 + r.size) past) (x ≤ l.size)
    simp only [changes, height]
    split
    · split
      · have := il (leftRequests l.size past) x; omega
      · split
        · omega
        · have := ir (rightRequests l.size past) (x - l.size - 1); omega
    · omega

theorem changeCost_bound (t : Tree) (past xs : List Nat) :
    changeCost t past xs ≤ xs.length * height t := by
  induction xs generalizing past with
  | nil => simp [changeCost]
  | cons x xs ih =>
    have := changes_le_height t past x
    have := ih (past ++ [x])
    simp only [changeCost, List.length_cons, Nat.add_mul]
    omega

theorem interleave_bound (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    interleave t xs ≤ xs.length * height t := by
  have heq := changeCost_eq t [] xs valid
  simp only [List.nil_append, interleave_nil, Nat.zero_add] at heq
  rw [heq]
  exact changeCost_bound t [] xs

theorem perfect_height (h : Nat) : height (perfect h) = h := by
  induction h with
  | zero => rfl
  | succ h ih => simp [perfect, height, ih, Nat.add_comm]

theorem perfect_size (h : Nat) : (perfect h).size = 2 ^ h - 1 := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [perfect, Tree.size, ih, Nat.pow_succ]
    have : 0 < 2 ^ h := Nat.two_pow_pos h
    omega

end RotationBST.Tango
