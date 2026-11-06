module

public import RotationBST.Structures.PopTart.Chocolate.Invariant
public import RotationBST.Structures.PopTart.Vanilla.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

/-- Collapsing a frozen interior into a fringe payload leaves the actual
physical BST exactly unchanged. -/
theorem outer_tree (icing : Icing) : icing.outer.tree = icing.decode.tree := by
  cases icing with
  | base crumb => rfl
  | solid crumb tail => exact congrArg (Tree.node crumb.tree) (outer_tree tail)
  | frozen carry old tail => exact congrArg (Tree.node (WeightedTree.node carry old.decode).tree) (outer_tree tail)
termination_by icing

theorem outer_mass (icing : Icing) : icing.outer.mass = icing.decode.mass := by
  cases icing with
  | base crumb => rfl
  | solid crumb tail => exact congrArg (crumb.mass + ·) (outer_mass tail)
  | frozen carry old tail => exact congrArg ((.node carry old.decode : WeightedTree).mass + ·) (outer_mass tail)
termination_by icing

/-- The frozen-block domination invariant is exactly the hypothesis of the
already verified Vanilla pop-tart. -/
theorem icing_vanilla {icing : Icing} {level : Nat} (valid : icing.Valid level) :
    Vanilla.Valid icing.outer := by
  cases icing with
  | base crumb => exact .leaf crumb.tree crumb.mass (mass_nonnegative valid.2)
  | solid crumb tail =>
    exact .push crumb.tree crumb.mass (icing_vanilla valid.2.2.1)
      (by simpa only [outer_mass] using valid.2.2.2)
  | frozen carry old tail =>
    exact .push (WeightedTree.node carry old.decode).tree (WeightedTree.node carry old.decode).mass
      (icing_vanilla valid.2.2.2.1)
      (by simpa only [outer_mass, mass] using valid.2.2.2.2.2)
termination_by icing

/-- Weighted outer access in the icing counts frozen blocks by their actual
mass. This does not yet bound depths inside a frozen block. -/
theorem icing_depth {icing : Icing} {level : Nat} (valid : icing.Valid level)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt icing.outer subtree weight depth) (positive : 0 < weight) :
    (depth : ℝ) ≤ 1 + Real.logb 2 (icing.decode.mass / weight) := by
  simpa only [outer_mass] using Vanilla.Results.depth_log (icing_vanilla valid) slot positive

theorem icing_access {icing : Icing} {level : Nat} (valid : icing.Valid level)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt icing.outer subtree weight depth) (positive : 0 < weight) (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.plug cs subtree = icing.decode.tree ∧
      Pointer.Trace ⟨icing.decode.tree, []⟩ ⟨subtree, cs⟩ depth ∧
      (depth : ℝ) ≤ 1 + Real.logb 2 (icing.decode.mass / weight) := by
  simpa only [outer_tree, outer_mass] using Vanilla.Results.access_slot (icing_vanilla valid) slot positive nonempty

end RotationBST.PopTart.Chocolate
