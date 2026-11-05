module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.MultipleTrees.Selection.AbstractBridge

@[expose] public section
namespace RotationBST.MultipleTrees.Selection.Results

theorem size (n capacity : Nat) (frequency : Nat → Nat) :
    (selected n capacity frequency).length = min capacity n := selected_length n capacity frequency

theorem distinct (n capacity : Nat) (frequency : Nat → Nat) :
    (selected n capacity frequency).Nodup := selected_distinct n capacity frequency

theorem valid (n capacity : Nat) (frequency : Nat → Nat) :
    ∀ x ∈ selected n capacity frequency, x < n := selected_valid n capacity frequency

theorem dominates (n capacity : Nat) (frequency : Nat → Nat) (x y : Nat)
    (stored : x ∈ selected n capacity frequency) (valid : y < n)
    (omitted : y ∉ selected n capacity frequency) : frequency y ≤ frequency x :=
  selected_dominates n capacity frequency x y stored valid omitted

theorem miss (n capacity : Nat) (frequency : Nat → Nat) (y : Nat)
    (fits : capacity ≤ n) (valid : y < n) (omitted : y ∉ selected n capacity frequency) :
    capacity * frequency y ≤ ((List.range n).map frequency).sum :=
  omitted_frequency n capacity frequency y fits valid omitted

theorem miss_information (n capacity : Nat) (frequency : Nat → Nat) (y : Nat)
    (fits : capacity ≤ n) (nonempty : 0 < capacity) (valid : y < n)
    (omitted : y ∉ selected n capacity frequency) (positive : 0 < frequency y) :
    Real.logb 2 capacity ≤ Real.logb 2 ((((List.range n).map frequency).sum : ℝ) / frequency y) :=
  omitted_information n capacity frequency y fits nonempty valid omitted positive

end RotationBST.MultipleTrees.Selection.Results

/-- info: abstract audit passed for `RotationBST.MultipleTrees.Selection.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.MultipleTrees.Selection.Results allowing [
  RotationBST.Algorithms.MultipleTrees.Selection.Definitions.Abstract]
