module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Finger.History.Rotation.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Rotation.Results
open Paired Recursive LabelledCursor Recursive.History

theorem rotateLeftChild {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.left parent sibling :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs l key (.node r parent sibling) next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 50 + s.potential ∧ next.ancestors = s.ancestors.tail :=
  RotationBST.HeavyPath.Finger.History.Rotation.rotateLeftChild valid

theorem rotateRightChild {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.right sibling parent :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs (.node sibling parent l) key r next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 50 + s.potential ∧ next.ancestors = s.ancestors.tail :=
  RotationBST.HeavyPath.Finger.History.Rotation.rotateRightChild valid

theorem rotateLeftChild_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.left parent sibling :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs l key (.node r parent sibling) next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 50 + s.potential ∧ next.ancestors = s.ancestors.tail ∧
      (cost : ℝ) ≤ 22 + 24 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Rotation.rotateLeftChild_bounded valid

theorem rotateRightChild_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.right sibling parent :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs (.node sibling parent l) key r next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 50 + s.potential ∧ next.ancestors = s.ancestors.tail ∧
      (cost : ℝ) ≤ 22 + 24 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Rotation.rotateRightChild_bounded valid

theorem rotateLeftChild_within {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.left parent sibling :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs l key (.node r parent sibling) next ∧
      Pointer.TraceWithin (fun t => t.size = s.pair.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth s.pair.tree x + 56) ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 50 + s.potential ∧ next.ancestors = s.ancestors.tail ∧
      (cost : ℝ) ≤ 22 + 24 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Rotation.rotateLeftChild_within valid

theorem rotateRightChild_within {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.right sibling parent :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs (.node sibling parent l) key r next ∧
      Pointer.TraceWithin (fun t => t.size = s.pair.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth s.pair.tree x + 56) ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 50 + s.potential ∧ next.ancestors = s.ancestors.tail ∧
      (cost : ℝ) ≤ 22 + 24 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Rotation.rotateRightChild_within valid

end RotationBST.HeavyPath.Finger.History.Rotation.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Finger.History.Rotation.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Finger.History.Rotation.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Invariant.Definitions.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.PopTart.Located.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Top.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.History.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Transfer.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract]
