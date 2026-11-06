module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Finger.Transfer.Exposure.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Transfer.Exposure.Results
open PopTart Recursive

theorem downLeft_exposed {p : Pair} (valid : p.Valid) {old a b : Tree} {oldCharge : ℝ}
    (stored : p.lower.top = .leaf old.mirror oldCharge) {exposureCost : Nat}
    (exposure : Pointer.Trace ⟨old, []⟩ ⟨.node a b, []⟩ exposureCost)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ cost, Pointer.Trace ⟨p.tree, []⟩ ⟨(p.downLeft a b lowerCharge upperCharge).tree, []⟩ cost ∧
      cost + (p.downLeft a b lowerCharge upperCharge).potential ≤ exposureCost + 30 + p.potential ∧
      (p.downLeft a b lowerCharge upperCharge).Valid ∧
      (p.downLeft a b lowerCharge upperCharge).mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk (p.downLeft a b lowerCharge upperCharge).tree []).key? =
        some (p.lower.decode.tree.mirror.size - b.size - 1) :=
  RotationBST.HeavyPath.Finger.Transfer.Exposure.downLeft_exposed valid stored exposure lowerNonnegative upperNonnegative

theorem downRight_exposed {p : Pair} (valid : p.Valid) {old a b : Tree} {oldCharge : ℝ}
    (stored : p.upper.top = .leaf old oldCharge) {exposureCost : Nat}
    (exposure : Pointer.Trace ⟨old, []⟩ ⟨.node a b, []⟩ exposureCost)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ cost, Pointer.Trace ⟨p.tree, []⟩ ⟨(p.downRight a b lowerCharge upperCharge).tree, []⟩ cost ∧
      cost + (p.downRight a b lowerCharge upperCharge).potential ≤ exposureCost + 30 + p.potential ∧
      (p.downRight a b lowerCharge upperCharge).Valid ∧
      (p.downRight a b lowerCharge upperCharge).mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk (p.downRight a b lowerCharge upperCharge).tree []).key? =
        some (p.lower.decode.tree.mirror.size + a.size + 1) :=
  RotationBST.HeavyPath.Finger.Transfer.Exposure.downRight_exposed valid stored exposure lowerNonnegative upperNonnegative

theorem downLeft_pair {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} {child : Paired.Stacks} (valid : p.Valid) (positive : Positive weight (.node l x r))
    (represented : child.Represents weight (rebuild weight) (extract weight (.node l x r)).context)
    {oldCharge : ℝ} (stored : p.lower.top = .leaf child.tree.mirror oldCharge)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ (view : Recursive.Exposure.View) (cost : Nat), view.Valid weight l r ∧
      let next := p.downLeft (view.leftTree weight l) (view.rightTree weight r) lowerCharge upperCharge
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + view.potential ≤ 54 + p.potential + child.potential ∧
      next.mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size - r.erase.size - 1) :=
  RotationBST.HeavyPath.Finger.Transfer.Exposure.downLeft_pair valid positive represented stored lowerNonnegative upperNonnegative

theorem downRight_pair {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} {child : Paired.Stacks} (valid : p.Valid) (positive : Positive weight (.node l x r))
    (represented : child.Represents weight (rebuild weight) (extract weight (.node l x r)).context)
    {oldCharge : ℝ} (stored : p.upper.top = .leaf child.tree oldCharge)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ (view : Recursive.Exposure.View) (cost : Nat), view.Valid weight l r ∧
      let next := p.downRight (view.leftTree weight l) (view.rightTree weight r) lowerCharge upperCharge
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + view.potential ≤ 54 + p.potential + child.potential ∧
      next.mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size + l.erase.size + 1) :=
  RotationBST.HeavyPath.Finger.Transfer.Exposure.downRight_pair valid positive represented stored lowerNonnegative upperNonnegative

theorem downLeft_recursive {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) (positive : Positive weight (.node l x r)) {oldCharge : ℝ}
    (stored : p.lower.top = .leaf (rebuild weight (.node l x r)).mirror oldCharge)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ (view : Recursive.Exposure.View) (cost : Nat), view.Valid weight l r ∧
      let next := p.downLeft (view.leftTree weight l) (view.rightTree weight r) lowerCharge upperCharge
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + view.potential ≤ 54 + p.potential + (rootPair weight (.node l x r)).potential ∧
      next.mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size - r.erase.size - 1) :=
  RotationBST.HeavyPath.Finger.Transfer.Exposure.downLeft_recursive valid positive stored lowerNonnegative upperNonnegative

theorem downRight_recursive {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) (positive : Positive weight (.node l x r)) {oldCharge : ℝ}
    (stored : p.upper.top = .leaf (rebuild weight (.node l x r)) oldCharge)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ (view : Recursive.Exposure.View) (cost : Nat), view.Valid weight l r ∧
      let next := p.downRight (view.leftTree weight l) (view.rightTree weight r) lowerCharge upperCharge
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + view.potential ≤ 54 + p.potential + (rootPair weight (.node l x r)).potential ∧
      next.mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size + l.erase.size + 1) :=
  RotationBST.HeavyPath.Finger.Transfer.Exposure.downRight_recursive valid positive stored lowerNonnegative upperNonnegative

theorem downLeft_source {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) (positive : Positive weight (.node l x r))
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.lower.top = .leaf (rebuild weight (.node l x r)).mirror (carry + mass weight (.node l x r))) :
    ∃ (view : Recursive.Exposure.View) (cost : Nat), view.Valid weight l r ∧
      let next := p.downLeft (view.leftTree weight l) (view.rightTree weight r)
        (carry + mass weight l) (fingerWeight + mass weight r)
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + view.potential ≤ 54 + p.potential + (rootPair weight (.node l x r)).potential ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size - r.erase.size - 1) :=
  RotationBST.HeavyPath.Finger.Transfer.Exposure.downLeft_source valid positive carryNonnegative fingerNonnegative stored

theorem downRight_source {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {p : Pair} (valid : p.Valid) (positive : Positive weight (.node l x r))
    {carry fingerWeight : ℝ} (carryNonnegative : 0 ≤ carry) (fingerNonnegative : 0 ≤ fingerWeight)
    (stored : p.upper.top = .leaf (rebuild weight (.node l x r)) (carry + mass weight (.node l x r))) :
    ∃ (view : Recursive.Exposure.View) (cost : Nat), view.Valid weight l r ∧
      let next := p.downRight (view.leftTree weight l) (view.rightTree weight r)
        (fingerWeight + mass weight l) (carry + mass weight r)
      Pointer.Trace ⟨p.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
      cost + next.potential + view.potential ≤ 54 + p.potential + (rootPair weight (.node l x r)).potential ∧
      next.mass + weight x = p.mass + fingerWeight ∧
      (Pointer.Config.mk next.tree []).key? = some (p.lower.decode.tree.mirror.size + l.erase.size + 1) :=
  RotationBST.HeavyPath.Finger.Transfer.Exposure.downRight_source valid positive carryNonnegative fingerNonnegative stored

theorem downLeft_exposed_bounded {p : Pair} (valid : p.Valid) {old a b : Tree} {oldCharge : ℝ}
    (stored : p.lower.top = .leaf old.mirror oldCharge) {exposureCost : Nat}
    (exposure : Pointer.Trace ⟨old, []⟩ ⟨.node a b, []⟩ exposureCost)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ cost, Pointer.Trace ⟨p.tree, []⟩ ⟨(p.downLeft a b lowerCharge upperCharge).tree, []⟩ cost ∧
      cost + (p.downLeft a b lowerCharge upperCharge).potential ≤ exposureCost + 30 + p.potential ∧
      (p.downLeft a b lowerCharge upperCharge).Valid ∧
      (p.downLeft a b lowerCharge upperCharge).mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk (p.downLeft a b lowerCharge upperCharge).tree []).key? =
        some (p.lower.decode.tree.mirror.size - b.size - 1) ∧
      cost ≤ exposureCost + p.upper.pushCost + 10 :=
  RotationBST.HeavyPath.Finger.Transfer.Exposure.downLeft_exposed_bounded valid stored exposure lowerNonnegative upperNonnegative

theorem downRight_exposed_bounded {p : Pair} (valid : p.Valid) {old a b : Tree} {oldCharge : ℝ}
    (stored : p.upper.top = .leaf old oldCharge) {exposureCost : Nat}
    (exposure : Pointer.Trace ⟨old, []⟩ ⟨.node a b, []⟩ exposureCost)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ cost, Pointer.Trace ⟨p.tree, []⟩ ⟨(p.downRight a b lowerCharge upperCharge).tree, []⟩ cost ∧
      cost + (p.downRight a b lowerCharge upperCharge).potential ≤ exposureCost + 30 + p.potential ∧
      (p.downRight a b lowerCharge upperCharge).Valid ∧
      (p.downRight a b lowerCharge upperCharge).mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk (p.downRight a b lowerCharge upperCharge).tree []).key? =
        some (p.lower.decode.tree.mirror.size + a.size + 1) ∧
      cost ≤ exposureCost + p.lower.pushCost + 10 :=
  RotationBST.HeavyPath.Finger.Transfer.Exposure.downRight_exposed_bounded valid stored exposure lowerNonnegative upperNonnegative

end RotationBST.HeavyPath.Finger.Transfer.Exposure.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Finger.Transfer.Exposure.Results`: 10 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Finger.Transfer.Exposure.Results allowing [
  RotationBST.Models.Rotation.Abstract,
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
  RotationBST.Structures.HeavyPath.Recursive.Exposure.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Transfer.Definitions.Abstract]
