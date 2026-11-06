module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Finger.Transfer.History.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Transfer.History.Results
open Recursive

theorem downLeft {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) {shape : Tree} {childCredit : Nat}
    (child : Recursive.History.Layout weight (.node l x r) shape childCredit)
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.lower.top = .leaf shape.mirror (carry + mass weight (.node l x r))) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Recursive.History.Layout weight l a leftCredit ∧ Recursive.History.Layout weight r b rightCredit ∧
      let next := p.downLeft a b (carry + mass weight l) (fingerWeight + mass weight r)
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + leftCredit + rightCredit ≤ 54 + p.potential + childCredit ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size - r.erase.size - 1) :=
  RotationBST.HeavyPath.Finger.Transfer.History.downLeft valid child carryNonnegative fingerNonnegative stored

theorem downRight {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) {shape : Tree} {childCredit : Nat}
    (child : Recursive.History.Layout weight (.node l x r) shape childCredit)
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.upper.top = .leaf shape (carry + mass weight (.node l x r))) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Recursive.History.Layout weight l a leftCredit ∧ Recursive.History.Layout weight r b rightCredit ∧
      let next := p.downRight a b (fingerWeight + mass weight l) (carry + mass weight r)
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + leftCredit + rightCredit ≤ 54 + p.potential + childCredit ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size + l.erase.size + 1) :=
  RotationBST.HeavyPath.Finger.Transfer.History.downRight valid child carryNonnegative fingerNonnegative stored

theorem downLeft_bounded {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) {shape : Tree} {childCredit : Nat}
    (child : Recursive.History.Layout weight (.node l x r) shape childCredit)
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.lower.top = .leaf shape.mirror (carry + mass weight (.node l x r))) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Recursive.History.Layout weight l a leftCredit ∧ Recursive.History.Layout weight r b rightCredit ∧
      let next := p.downLeft a b (carry + mass weight l) (fingerWeight + mass weight r)
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + leftCredit + rightCredit ≤ 54 + p.potential + childCredit ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size - r.erase.size - 1) ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 p.tree.size :=
  RotationBST.HeavyPath.Finger.Transfer.History.downLeft_bounded valid child carryNonnegative fingerNonnegative stored

theorem downRight_bounded {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) {shape : Tree} {childCredit : Nat}
    (child : Recursive.History.Layout weight (.node l x r) shape childCredit)
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.upper.top = .leaf shape (carry + mass weight (.node l x r))) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Recursive.History.Layout weight l a leftCredit ∧ Recursive.History.Layout weight r b rightCredit ∧
      let next := p.downRight a b (fingerWeight + mass weight l) (carry + mass weight r)
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + leftCredit + rightCredit ≤ 54 + p.potential + childCredit ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size + l.erase.size + 1) ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 p.tree.size :=
  RotationBST.HeavyPath.Finger.Transfer.History.downRight_bounded valid child carryNonnegative fingerNonnegative stored

theorem downLeft_within {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) {shape : Tree} {childCredit : Nat}
    (child : Recursive.History.Layout weight (.node l x r) shape childCredit)
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.lower.top = .leaf shape.mirror (carry + mass weight (.node l x r))) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Recursive.History.Layout weight l a leftCredit ∧ Recursive.History.Layout weight r b rightCredit ∧
      let next := p.downLeft a b (carry + mass weight l) (fingerWeight + mass weight r)
      Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth p.tree x + 64) ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + leftCredit + rightCredit ≤ 54 + p.potential + childCredit ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size - r.erase.size - 1) ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 p.tree.size :=
  RotationBST.HeavyPath.Finger.Transfer.History.downLeft_within valid child carryNonnegative fingerNonnegative stored

theorem downRight_within {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) {shape : Tree} {childCredit : Nat}
    (child : Recursive.History.Layout weight (.node l x r) shape childCredit)
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.upper.top = .leaf shape (carry + mass weight (.node l x r))) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Recursive.History.Layout weight l a leftCredit ∧ Recursive.History.Layout weight r b rightCredit ∧
      let next := p.downRight a b (fingerWeight + mass weight l) (carry + mass weight r)
      Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth p.tree x + 64) ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + leftCredit + rightCredit ≤ 54 + p.potential + childCredit ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size + l.erase.size + 1) ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 p.tree.size :=
  RotationBST.HeavyPath.Finger.Transfer.History.downRight_within valid child carryNonnegative fingerNonnegative stored

end RotationBST.HeavyPath.Finger.Transfer.History.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Finger.Transfer.History.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Finger.Transfer.History.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Models.Pointer.Invariant.Definitions.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Top.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.History.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Transfer.Definitions.Abstract]
