module

import RotationBST.Audit.Check
public import RotationBST.Bounds.LazyFinger.Dynamic.AbstractBridge

@[expose] public section
namespace RotationBST.LazyFinger.Dynamic.Results

/-- Realize the lazy-finger distance by exactly that many pointer instructions.
The endpoints are cursors on the fixed reference tree. -/
theorem walk (t : Tree) (x y : Nat) (hx : x < t.size) (hy : y < t.size) :
    ∃ a b : Pointer.Config, a.tree = t ∧ b.tree = t ∧ a.key? = some x ∧ b.key? = some y ∧
      Pointer.Trace a b (distance t x y) := pointer_walk t x y hx hy

/-- The realizing path uses only navigation, with no intervening rotations. -/
theorem readonly (t : Tree) (x y : Nat) (hx : x < t.size) (hy : y < t.size) :
    ∃ a b : Pointer.Config, a.tree = t ∧ b.tree = t ∧ a.key? = some x ∧ b.key? = some y ∧
      Pointer.Walk a b (distance t x y) := readonly_walk t x y hx hy

/-- The edge metric is a lower bound for every navigation-only walk. -/
theorem shortest {a b : Pointer.Config} {k : Nat} (walk : Pointer.Walk a b k)
    (x y : Nat) (keyA : a.key? = some x) (keyB : b.key? = some y) : distance a.tree x y ≤ k :=
  distance_le_walk walk x y keyA keyB

/-- A shortest route can be followed one legal parent/child instruction at a time. -/
theorem toward (a : Pointer.Config) (x y : Nat) (key : a.key? = some x)
    (valid : y < a.tree.size) (different : x ≠ y) :
    ∃ b z, Pointer.Move a b ∧ b.key? = some z ∧ distance b.tree z y + 1 = distance a.tree x y :=
  toward_exists a x y key valid different

/-- Retaining one finger between requests gives exactly the lazy-finger cost. -/
theorem persistent (t : Tree) (p : Nat) (xs : List Nat) (hp : p < t.size)
    (valid : ∀ x ∈ xs, x < t.size) :
    ∃ q : Nat, Multifinger.Execution (⟨t, fun _ : Fin 1 => p⟩ : Multifinger.State 1) xs
      ⟨t, fun _ => q⟩ (costFrom t p xs) := multifinger_execution t p xs hp valid

/-- A conventional dynamic execution from the same initial tree, with constant
factor overhead. Each request starts at the root in the target machine. -/
theorem same_tree (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    ∃ u k, Pointer.Execution t xs u k ∧ k ≤ 464 * cost t xs := dynamic_execution t xs valid

/-- When the initial tree may be chosen, there is no startup term. The selected
initial tree may depend on the whole sequence. -/
theorem optimal_tree (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    ∃ t u k, t.size = n ∧ Pointer.Execution t xs u k ∧ k ≤ 464 * optimalCost n xs :=
  dynamic_optimal_tree n xs valid

/-- An arbitrary fixed initial tree, with explicit cost to reshape it to the
reference tree. This also includes the empty sequence and empty universe. -/
theorem reference (s t : Tree) (xs : List Nat) (same : s.size = t.size)
    (valid : ∀ x ∈ xs, x < t.size) :
    ∃ u k, Pointer.Execution s xs u k ∧ k ≤ 16 * s.size + 464 * cost t xs :=
  dynamic_reference_tree s t xs same valid

/-- The dynamic/lazy inequality of Theorem 6 of arXiv:1304.6897, stated as a
legal offline execution witness from any prescribed initial tree. This does
not assert an online choice of the optimal reference tree. -/
theorem optimal (s : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < s.size) :
    ∃ u k, Pointer.Execution s xs u k ∧ k ≤ 16 * s.size + 464 * optimalCost s.size xs :=
  dynamic_optimal s xs valid

/-- For `m ≥ n`, normalized request charges absorb initialization. -/
theorem long_sequence (s : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < s.size) (long : s.size ≤ xs.length) :
    ∃ u k, Pointer.Execution s xs u k ∧ k ≤ 480 * optimalCost s.size xs :=
  dynamic_optimal_long s xs valid long

end RotationBST.LazyFinger.Dynamic.Results

/-- info: abstract audit passed for `RotationBST.LazyFinger.Dynamic.Results`: 10 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.LazyFinger.Dynamic.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Walk.Definitions.Abstract,
  RotationBST.Models.Multifinger.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract]
