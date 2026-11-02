module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.Reference.Bounds

@[expose] public section
namespace RotationBST.Tango.Reference.Results

/-- The executable reference constructor works for every key count, including
zero, and has logarithmic height. No padding keys are introduced. -/
theorem balanced_reference (n : Nat) :
    (balanced n).size = n ∧ height (balanced n) ≤ Nat.log2 n + 1 :=
  ⟨balanced_size n, balanced_height n⟩

end RotationBST.Tango.Reference.Results

#check_bst_abstract RotationBST.Tango.Reference.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.Definitions.Abstract,
  RotationBST.Tango.Reference.Abstract]
