module

import RotationBST.Audit.Check
public import RotationBST.Models.Pointer.Lazy.Online.Abstract
public import RotationBST.Models.Pointer.Lazy.Abstract
public import RotationBST.Models.Pointer.AbstractBridge

@[expose] public section

/-! The single-cursor machine is defined in `Models/Pointer/Machine/Abstract`:
unit-cost parent/child moves and rotations, starting at the root for each search,
visiting the requested rank, and charging one additional unit per request.

The simulations agree up to constant factors in request-plus-instruction cost.
A final deferred rotation suffix is explicit in both directions. Exact endpoint
agreement is also available with a size-dependent eager bound. -/
namespace RotationBST.Pointer.Results

variable {s t : Tree} {xs : List Nat} {k : Nat}

/-- Conventional searches become root accesses with at most factor three in
total cost. Final pending rotations are retained and charged explicitly. -/
theorem to_rotations (h : Pointer.Execution s xs t k) :
    ∃ u r q, RotationBST.Execution s xs u r ∧ Rotations u t q ∧
      xs.length + r + q ≤ 3 * k :=
  Pointer.execution_to_rotations h

/-- Lazy simulation has constant overhead, independent of tree size. Its final
pending rotations are explicitly retained and charged. -/
theorem to_pointer_lazy (h : RotationBST.Execution s xs t k) :
    ∃ u c d, Pointer.Execution s xs u c ∧ Rotations u t d ∧
      c + 32 * d ≤ 32 * k + 17 * xs.length :=
  Lazy.execution_to_pointer h

/-- Eager simulation preserves the exact final shape. Navigating to arbitrary
deep rotations incurs the displayed tree-size factor. -/
theorem to_pointer (h : RotationBST.Execution s xs t k) :
    ∃ m, m ≤ xs.length + 2 * s.size * k ∧ Pointer.Execution s xs t m :=
  Pointer.execution_to_pointer h

end RotationBST.Pointer.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
/-- info: abstract audit passed for `RotationBST.Pointer.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Pointer.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract]
