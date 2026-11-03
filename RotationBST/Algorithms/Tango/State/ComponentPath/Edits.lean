module

public import RotationBST.Algorithms.Tango.State.ComponentPath.Proofs
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Simulation

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Execute an interval cut at a component path, with the reference nesting and
local component size controlling the result and its amortized cost. -/
theorem cut_at_path (s reference child : MarkedTree) (path : List Nat) (i j : Nat)
    (same : s.nesting = reference.nesting) (found : reference.componentAt path = some child)
    (ordered : i < j) (valid : j ≤ child.region.size) (proper : j - i < child.region.size) :
    (s.editAt path (fun t => t.cutInterval i j)).1.nesting =
        reference.nesting.replaceAt path (child.nesting.group i (j - i + 1)) ∧
      Rotations s.tree (s.editAt path (fun t => t.cutInterval i j)).1.tree
        (s.editAt path (fun t => t.cutInterval i j)).2 ∧
      ((s.editAt path (fun t => t.cutInterval i j)).2 : ℝ) +
        (s.editAt path (fun t => t.cutInterval i j)).1.potential - s.potential ≤
          6 * Real.logb 2 child.region.size + 2 := by
  have nonempty : child ≠ .nil := by intro h; subst child; simp [region, Pointer.Lazy.Skeleton.size] at valid; omega
  exact editAt_simulates path s reference child _ _ _ same found nonempty
    (fun actual nested => cutInterval_simulates actual child nested i j ordered valid proper)

/-- Execute an attached-component merge at arbitrary component depth. -/
theorem merge_at_path (s reference child attached : MarkedTree) (path : List Nat) (i : Nat)
    (same : s.nesting = reference.nesting) (found : reference.componentAt path = some child)
    (positive : 0 < child.region.size) (valid : i ≤ child.region.size)
    (slot : child.fringe[i]? = some attached) :
    (s.editAt path (fun t => t.mergeAt i)).1.nesting =
        reference.nesting.replaceAt path (child.nesting.merge i) ∧
      Rotations s.tree (s.editAt path (fun t => t.mergeAt i)).1.tree
        (s.editAt path (fun t => t.mergeAt i)).2 ∧
      ((s.editAt path (fun t => t.mergeAt i)).2 : ℝ) +
        (s.editAt path (fun t => t.mergeAt i)).1.potential - s.potential ≤
          8 * Real.logb 2 (child.region.size + attached.region.size : Nat) + 2 := by
  have nonempty : child ≠ .nil := by intro h; subst child; exact Nat.not_lt_zero _ positive
  exact editAt_simulates path s reference child _ _ _ same found nonempty
    (fun actual nested => mergeAt_simulates actual child attached nested i positive valid slot)

end RotationBST.Tango.MarkedTree
