module

import RotationBST.Audit.Check
public import RotationBST.Bounds.LazyFinger.Edges.AbstractBridge

@[expose] public section
namespace RotationBST.LazyFinger.Edges.Results

/-- A transition with both endpoints outside a subtree uses no internal edges. -/
theorem outside (t : Tree) (lo x y : Nat)
    (hx : ¬ (lo ≤ x ∧ x < lo + t.size))
    (hy : ¬ (lo ≤ y ∧ y < lo + t.size)) : edgeMovement t lo x y = 0 :=
  edgeMovement_outside t lo x y hx hy

/-- Entering or leaving uses the endpoint's root path and one incoming edge. -/
theorem entering (t : Tree) (lo x y : Nat)
    (hx : lo ≤ x ∧ x < lo + t.size)
    (hy : ¬ (lo ≤ y ∧ y < lo + t.size)) :
    edgeMovement t lo x y = Tree.depth t (x - lo) + 1 := edgeMovement_enter t lo x y hx hy

/-- Summing subtree-boundary crossings gives the exact distance between keys. -/
theorem distance (t : Tree) (lo x y : Nat)
    (hx : lo ≤ x ∧ x < lo + t.size) (hy : lo ≤ y ∧ y < lo + t.size) :
    edgeMovement t lo x y = LazyFinger.distance t (x - lo) (y - lo) :=
  edgeMovement_inside t lo x y hx hy

/-- Sequence cost is the request count plus the sum of all boundary crossings. -/
theorem sequence (t : Tree) (p : Nat) (xs : List Nat)
    (hp : p < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    costFrom t p xs = xs.length + intervalCost (fun a b => crossings a b p xs) t 0 :=
  costFrom_eq_crossings t p xs hp valid

/-- The external initial key adds exactly one edge on a nonempty sequence,
independently of the shape's root. This converts root initialization to a fixed
boundary objective for interval optimization. -/
theorem initialization (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    cost t xs + (if xs = [] then 0 else 1) =
      xs.length + intervalCost (fun a b => crossings a b t.size xs) t 0 :=
  cost_eq_crossings t xs valid

/-- One rotation replaces one proper-subtree interval, so bounded boundary
tolls have bounded sensitivity to any single rotation. -/
theorem rotation (w : Nat → Nat → Nat) (C : Nat) (bounded : ∀ lo hi, w lo hi ≤ C)
    {s t : Tree} (rotation : Rotate s t) (lo : Nat) :
    intervalCost w t lo ≤ intervalCost w s lo + C := intervalCost_rotate_le w C bounded rotation lo

/-- The same stability applies to normalized sequence cost. -/
theorem sequence_rotation {s t : Tree} (rotation : Rotate s t) (p : Nat) (xs : List Nat)
    (initial : p < s.size) (valid : ∀ x ∈ xs, x < s.size) (C : Nat)
    (bounded : ∀ lo hi, crossings lo hi p xs ≤ C) :
    costFrom t p xs ≤ costFrom s p xs + C := costFrom_rotate_le rotation p xs initial valid C bounded

end RotationBST.LazyFinger.Edges.Results

/-- info: abstract audit passed for `RotationBST.LazyFinger.Edges.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.LazyFinger.Edges.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Edges.Definitions.Abstract]
