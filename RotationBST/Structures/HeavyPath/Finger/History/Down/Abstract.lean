module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Finger.History.Down.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Down.Results
open Paired Recursive LabelledCursor Recursive.History

theorem downLeft {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key x : α} {s : State α}
    (valid : Valid weight cs (.node l x r) key sibling s) :
    ∃ (next : State α) (cost : Nat), Valid weight (.left key sibling :: cs) l x r next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 54 + s.potential ∧
      next.ancestors = ⟨.left key sibling, s.rightShape, s.rightCredit⟩ :: s.ancestors :=
  RotationBST.HeavyPath.Finger.History.Down.downLeft valid

theorem downRight {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key x : α} {s : State α}
    (valid : Valid weight cs sibling key (.node l x r) s) :
    ∃ (next : State α) (cost : Nat), Valid weight (.right sibling key :: cs) l x r next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 54 + s.potential ∧
      next.ancestors = ⟨.right sibling key, s.leftShape, s.leftCredit⟩ :: s.ancestors :=
  RotationBST.HeavyPath.Finger.History.Down.downRight valid

theorem downLeft_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key x : α} {s : State α}
    (valid : Valid weight cs (.node l x r) key sibling s) :
    ∃ (next : State α) (cost : Nat), Valid weight (.left key sibling :: cs) l x r next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 54 + s.potential ∧
      next.ancestors = ⟨.left key sibling, s.rightShape, s.rightCredit⟩ :: s.ancestors ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Down.downLeft_bounded valid

theorem downRight_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key x : α} {s : State α}
    (valid : Valid weight cs sibling key (.node l x r) s) :
    ∃ (next : State α) (cost : Nat), Valid weight (.right sibling key :: cs) l x r next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 54 + s.potential ∧
      next.ancestors = ⟨.right sibling key, s.leftShape, s.leftCredit⟩ :: s.ancestors ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Down.downRight_bounded valid

theorem downLeft_within {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key x : α} {s : State α}
    (valid : Valid weight cs (.node l x r) key sibling s) :
    ∃ (next : State α) (cost : Nat), Valid weight (.left key sibling :: cs) l x r next ∧
      Pointer.TraceWithin (fun t => t.size = s.pair.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth s.pair.tree x + 64) ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 54 + s.potential ∧
      next.ancestors = ⟨.left key sibling, s.rightShape, s.rightCredit⟩ :: s.ancestors ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Down.downLeft_within valid

theorem downRight_within {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key x : α} {s : State α}
    (valid : Valid weight cs sibling key (.node l x r) s) :
    ∃ (next : State α) (cost : Nat), Valid weight (.right sibling key :: cs) l x r next ∧
      Pointer.TraceWithin (fun t => t.size = s.pair.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth s.pair.tree x + 64) ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 54 + s.potential ∧
      next.ancestors = ⟨.right sibling key, s.leftShape, s.leftCredit⟩ :: s.ancestors ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Down.downRight_within valid

end RotationBST.HeavyPath.Finger.History.Down.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Finger.History.Down.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Finger.History.Down.Results allowing [
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
