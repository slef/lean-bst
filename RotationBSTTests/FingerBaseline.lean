module

public import RotationBST.Bounds.DynamicFinger.Abstract
public import RotationBST.Bounds.Implications.Abstract
public import RotationBST.Classical.Static.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.FingerBaseline
open _root_.RotationBST.Tree (balanced)
open Classical.Static

private def one : Tree := .node .nil .nil
private def three : Tree := .node one one
private def seven : Tree := .node three three
private def path : Nat → Tree
  | 0 => .nil
  | n + 1 => .node .nil (path n)

-- The balanced tree on `2^k - 1` keys is the perfect tree; its shape on six
-- keys puts the larger half on the left.
example : balanced 7 = seven := by decide +kernel
example : balanced 6 = .node three (.node one .nil) := by decide +kernel
example : (List.range 7).map seven.depth = [2, 1, 2, 0, 2, 1, 2] := by decide
example : (List.range 8).map (balanced 8).depth = [3, 2, 1, 2, 0, 2, 1, 2] := by decide +kernel
example : (balanced 8).depth 0 = Nat.log2 8 := by decide +kernel

-- The depth bound is tight at a power of two and the deep key exists for any shape.
example : (balanced 1000).depth 999 ≤ 9 := Results.balanced_depth 1000 999 (by omega)
example : ∃ x < (path 5).size, Nat.log2 (path 5).size ≤ (path 5).depth x :=
  Results.exists_deep (path 5) (by decide)
example : StaticTree.cost seven [0, 3, 6] = 3 + 1 + 3 := by decide
example : StaticTree.cost (balanced 7) [0, 3, 6, 6] ≤ 4 * 3 :=
  Results.balanced_cost 7 [0, 3, 6, 6] (by decide)
example : ∃ x < seven.size, 5 * 3 ≤ StaticTree.cost seven (List.replicate 5 x) :=
  Results.exists_expensive seven (by decide) 5

-- The dynamic-finger inequality with a start key away from the finger, and
-- with the start key at the finger.
example : Bounds.dynamicFingerCostFrom 9 [0, 7, 3] ≤
    2 * Bounds.fingerCost 4 [0, 7, 3] + Real.logb 2 (Nat.dist 9 4 + 1 : Nat) :=
  Bounds.dynamicFinger_le_fingerCost 4 9 [0, 7, 3]
example : Bounds.dynamicFingerCostFrom 4 [] = 0 := rfl
example (xs : List Nat) : Bounds.dynamicFingerCostFrom 2 xs ≤ 2 * Bounds.fingerCost 2 xs :=
  Bounds.dynamicFinger_le_fingerCost_self 2 xs
example : Bounds.fingerCost 3 [0, 6] ≤ Bounds.logCost 7 [0, 6] :=
  Bounds.fingerCost_le_log 7 3 [0, 6] (by omega) (by decide)

-- The chain of properties DF ⇒ SF ⇒ logarithmic.
example (a : Algorithm) (h : HasDynamicFingerBound a) : HasLogarithmicBound a :=
  Bounds.staticFinger_implies_logarithmic a (Bounds.dynamicFinger_implies_staticFinger a h)

end RotationBST.Tests.FingerBaseline
