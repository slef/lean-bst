module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Reference.Bounds

@[expose] public section
namespace RotationBST.Tango.Reference.Results

/-- The executable reference constructor works for every key count, including
zero, and has logarithmic height. No padding keys are introduced. -/
theorem balanced_reference (n : Nat) :
    (balanced n).size = n ∧ height (balanced n) ≤ Nat.log2 n + 1 :=
  ⟨balanced_size n, balanced_height n⟩

end RotationBST.Tango.Reference.Results

#check_bst_abstract RotationBST.Tango.Reference.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Bounds.Interleave.Definitions.Abstract, RotationBST.Algorithms.Tango.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Reference.Abstract]
