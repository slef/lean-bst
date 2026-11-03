module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Splay.Scanning.Abstract
public import RotationBST.Algorithms.Splay.Updates.Abstract
public import RotationBST.Algorithms.Splay.Conditional.Abstract
public import RotationBST.Algorithms.Splay.Snapshot.Abstract
public import RotationBST.Algorithms.Splay.AbstractBridge
public import RotationBST.Algorithms.Splay.AccessLemma.Abstract
public import RotationBST.Algorithms.Splay.Balance.Abstract
public import RotationBST.Algorithms.Splay.WorkingSet.Abstract
public import RotationBST.Algorithms.Splay.StaticOptimality.Abstract
public import RotationBST.Algorithms.Splay.StaticFinger.Abstract
public import RotationBST.Algorithms.Splay.Unified.Abstract

@[expose] public section

/-! Splay overview. The executable bottom-up zig/zig-zig/zig-zag definition is
in `Algorithms/Splay/Algorithm/Abstract`; each analytic result has its own short abstract.
The online algorithm uses only its current shape, with no weights or history. -/
namespace RotationBST.Splay.Results

/-- Splay exposes exactly the requested rank using a legal rotation trace.
Its rotation count is the depth of that rank, hence less than the number of nodes. -/
theorem correct (t : Tree) (x : Nat) (valid : x < t.size) :
    Access t (run t x).1 x (run t x).2 ∧ (run t x).2 < t.size :=
  run_correct t x valid

/-- This concrete splay algorithm has a constant-factor pointer implementation
with exactly the same final shape. -/
theorem pointer_execution (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    ∃ k, k ≤ 3 * algorithm.totalCost t xs ∧
      Pointer.Execution t xs (algorithm.runFrom [] t xs).1 k :=
  Bridge.pointer_execution t xs valid

/-- Working set in the conventional pointer-and-rotation cost model. -/
theorem pointer_workingSet (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    ∃ k, k ≤ 31 * workingSetSum t.size [] xs + 18 * t.size * (1 + t.size.log2) ∧
      Pointer.Execution t xs (algorithm.runFrom [] t xs).1 k :=
  Bridge.pointer_workingSet t xs valid

end RotationBST.Splay.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
/-- info: abstract audit passed for `RotationBST.Splay.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Splay.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Online.Abstract,
  RotationBST.Bounds.WorkingSet.Abstract]
