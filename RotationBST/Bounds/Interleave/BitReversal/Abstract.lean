module

import RotationBST.Audit.Check
public import RotationBST.Bounds.Interleave.BitReversal.AbstractBridge

@[expose] public section
namespace RotationBST.Wilber.BitReversal.Results

theorem size (h : Nat) : (reference h).size + 1 = 2 ^ (h + 1) := reference_size h

theorem length (h : Nat) : (requests h).length = 2 ^ h := requests_length h

theorem valid (h : Nat) : ∀ x ∈ requests h, x < (reference h).size := requests_valid h

theorem distinct (h : Nat) : (requests h).Nodup := requests_distinct h

/-- Bit reversal forces a logarithmic interleave count per requested leaf. -/
theorem lower (h : Nat) : h * 2 ^ h ≤ 2 * interleave (reference h) (requests h) := interleave_lower h

/-- Every conventional dynamic BST pays for these interleaves, across repeated
periods without resetting its physical state. -/
theorem pointer (h rounds : Nat) {s t : Tree} {k : Nat}
    (same : s.size = (reference h).size)
    (run : Pointer.Execution s (ConditionalEntropy.repeatPeriod (requests h) rounds) t k) :
    h * (ConditionalEntropy.repeatPeriod (requests h) rounds).length ≤ 24 * k :=
  repeated_pointer_lower h rounds same run

/-- Lower bound in the simplified arbitrary-rotation model, with request costs
kept explicit. -/
theorem rotations (h rounds : Nat) {s t : Tree} {k : Nat}
    (same : s.size = (reference h).size)
    (run : RotationBST.Execution s (ConditionalEntropy.repeatPeriod (requests h) rounds) t k) :
    h * (ConditionalEntropy.repeatPeriod (requests h) rounds).length ≤
      8 * k + 4 * (ConditionalEntropy.repeatPeriod (requests h) rounds).length :=
  repeated_rotation_lower h rounds same run

end RotationBST.Wilber.BitReversal.Results

/-- info: abstract audit passed for `RotationBST.Wilber.BitReversal.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Wilber.BitReversal.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Bounds.Interleave.Definitions.Abstract,
  RotationBST.Bounds.Interleave.BitReversal.Definitions.Abstract,
  RotationBST.Bounds.ConditionalEntropy.Definitions.Abstract]
