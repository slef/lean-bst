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

/-- A reference tree and an existing key uniquely determine the complete
cursor, including its focused subtree and enclosing zipper. -/
theorem cursor_unique {a b : Config} {x : Nat} (tree : a.tree = b.tree)
    (left : a.key? = some x) (right : b.key? = some x) : a = b :=
  Config.ext_key tree left right

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

/-- Changing the initial shape costs at most sixteen physical instructions
per key and leaves the pointer at the root. -/
theorem reshape (s t : Tree) (same : s.size = t.size) :
    ∃ k, k ≤ 16 * s.size ∧ Trace ⟨s, []⟩ ⟨t, []⟩ k := Pointer.reshape s t same

/-- A fixed cursor can reach at most exponentially many different keys with a
bounded number of physical instructions, even when rotations are permitted. -/
theorem reachable_keys (a : Config) (r : Nat) (keys : Finset Nat)
    (reachable : ∀ x ∈ keys, ∃ b k, Trace a b k ∧ k ≤ r ∧ b.key? = some x) :
    keys.card ≤ 7 ^ r := reachable_keys_card a r keys reachable

end RotationBST.Pointer.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
/-- info: abstract audit passed for `RotationBST.Pointer.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Pointer.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract]
