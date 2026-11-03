module

public import RotationBST.Bounds.Interleave.Definitions.Abstract
import Mathlib.Data.List.Induction

@[expose] public section
namespace RotationBST.Tango

theorem alternations_append (xs : List Bool) (x : Bool) :
    alternations (xs ++ [x]) = alternations xs + switch xs x := by
  induction xs using List.twoStepInduction with
  | nil => simp [alternations, switch]
  | singleton a => simp [alternations, switch]
  | cons_cons a b xs _ ih =>
    simpa [alternations, switch, List.getLast?_cons_cons, Nat.add_assoc] using (ih b)

theorem regions_append (l n : Nat) (xs ys : List Nat) :
    regions l n (xs ++ ys) = regions l n xs ++ regions l n ys := by
  simp [regions]

theorem left_append (l : Nat) (xs ys : List Nat) :
    leftRequests l (xs ++ ys) = leftRequests l xs ++ leftRequests l ys := by
  simp [leftRequests]

theorem right_append (l : Nat) (xs ys : List Nat) :
    rightRequests l (xs ++ ys) = rightRequests l xs ++ rightRequests l ys := by
  simp [rightRequests]

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

theorem interleave_nil (t : Tree) : interleave t [] = 0 := by
  induction t with
  | nil => rfl
  | node l r il ir => simp [interleave, regions, alternations, leftRequests, rightRequests, il, ir]

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

end RotationBST.Tango
