module

public import RotationBST.Algorithms.Tango.Preferences.Initialization.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Reference.Abstract
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section
namespace RotationBST.Tango.Initialization

/-- Height of the reference subtree rooted at an inorder key; zero off-tree. -/
def heightAt : Tree → Nat → Nat
  | .nil, _ => 0
  | .node l r, key =>
      if key < l.size then heightAt l key
      else if key = l.size then height (.node l r)
      else heightAt r (key - l.size - 1)

/-- Sum of subtree heights, used only to bound available initialization credit. -/
def heightSum : Tree → Nat
  | .nil => 0
  | .node l r => height (.node l r) + heightSum l + heightSum r

/-- Local reference-height credit. This is not the evolving component charge. -/
noncomputable def localCredit (t : Tree) (key : Nat) : ℝ :=
  8 * Real.logb 2 (heightAt t key) + 2

/-- One local logarithmic allowance at each node of the reference tree. -/
noncomputable def localAllowance : Tree → ℝ
  | .nil => 0
  | .node l r => 8 * Real.logb 2 (height (.node l r)) + 2 + localAllowance l + localAllowance r

end RotationBST.Tango.Initialization
