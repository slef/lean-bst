module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Recursive.Exposure.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.Exposure.Results
open Paired LabelledCursor

theorem rootPair_represents {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) :
    (rootPair weight t).Represents weight (rebuild weight) (extract weight t).context :=
  RotationBST.HeavyPath.Recursive.Exposure.rootPair_represents positive

theorem represented_size {α : Type} {weight : α → ℝ} {t : LabelledTree α} {p : Stacks}
    (positive : Positive weight t) (nonempty : t ≠ .nil)
    (represented : p.Represents weight (rebuild weight) (extract weight t).context) :
    p.tree.size = t.erase.size :=
  RotationBST.HeavyPath.Recursive.Exposure.represented_size positive nonempty represented

theorem expose_left {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    (positive : Positive weight (.node l x r)) (heavy : LeftHeavy weight l r) (nonempty : l ≠ .nil) :
    ∃ rest : Stacks,
      rest.Represents weight (rebuild weight) (extract weight l).context ∧
      Pointer.Trace ⟨rebuild weight (.node l x r), []⟩
        ⟨.node rest.tree (rebuild weight r), []⟩ ((rootPair weight (.node l x r)).exposeCost (.left x r)) ∧
      (rootPair weight (.node l x r)).exposeCost (.left x r) + rest.potential ≤
        24 + (rootPair weight (.node l x r)).potential ∧
      rest.tree.size = l.erase.size ∧
      (rootPair weight (.node l x r)).mass = rest.mass + (weight x + mass weight r) :=
  RotationBST.HeavyPath.Recursive.Exposure.expose_left positive heavy nonempty

theorem expose_right {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    (positive : Positive weight (.node l x r)) (heavy : ¬ LeftHeavy weight l r) (nonempty : r ≠ .nil) :
    ∃ rest : Stacks,
      rest.Represents weight (rebuild weight) (extract weight r).context ∧
      Pointer.Trace ⟨rebuild weight (.node l x r), []⟩
        ⟨.node (rebuild weight l) rest.tree, []⟩ ((rootPair weight (.node l x r)).exposeCost (.right l x)) ∧
      (rootPair weight (.node l x r)).exposeCost (.right l x) + rest.potential ≤
        24 + (rootPair weight (.node l x r)).potential ∧
      rest.tree.size = r.erase.size ∧
      (rootPair weight (.node l x r)).mass = rest.mass + (mass weight l + weight x) :=
  RotationBST.HeavyPath.Recursive.Exposure.expose_right positive heavy nonempty

theorem root_exposure {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    (positive : Positive weight (.node l x r)) :
    ∃ (a b : Tree) (cost remainingPotential : Nat),
      Pointer.Trace ⟨rebuild weight (.node l x r), []⟩ ⟨.node a b, []⟩ cost ∧
      a.size = l.erase.size ∧ b.size = r.erase.size ∧
      (Pointer.Config.mk (.node a b) []).key? = some l.erase.size ∧
      cost + remainingPotential ≤ 24 + (rootPair weight (.node l x r)).potential :=
  RotationBST.HeavyPath.Recursive.Exposure.root_exposure positive

theorem expose_pair_view {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α} {p : Stacks}
    (positive : Positive weight (.node l x r))
    (represented : p.Represents weight (rebuild weight) (extract weight (.node l x r)).context) :
    ∃ (view : View) (cost : Nat), view.Valid weight l r ∧
      Pointer.Trace ⟨p.tree, []⟩
        ⟨.node (view.leftTree weight l) (view.rightTree weight r), []⟩ cost ∧
      (view.leftTree weight l).size = l.erase.size ∧
      (view.rightTree weight r).size = r.erase.size ∧
      cost + view.potential ≤ 24 + p.potential :=
  RotationBST.HeavyPath.Recursive.Exposure.expose_pair_view positive represented

theorem expose_view {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    (positive : Positive weight (.node l x r)) :
    ∃ (view : View) (cost : Nat), view.Valid weight l r ∧
      Pointer.Trace ⟨rebuild weight (.node l x r), []⟩
        ⟨.node (view.leftTree weight l) (view.rightTree weight r), []⟩ cost ∧
      (view.leftTree weight l).size = l.erase.size ∧
      (view.rightTree weight r).size = r.erase.size ∧
      cost + view.potential ≤ 24 + (rootPair weight (.node l x r)).potential :=
  RotationBST.HeavyPath.Recursive.Exposure.expose_view positive

end RotationBST.HeavyPath.Recursive.Exposure.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Recursive.Exposure.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Recursive.Exposure.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.Exposure.Definitions.Abstract]
