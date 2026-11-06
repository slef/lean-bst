module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Finger.History.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Results
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree Recursive.History

theorem state_mass {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α} (valid : Valid weight cs left key right s) :
    weight key + s.pair.mass = HeavyPath.mass weight (plug cs (.node left key right)) :=
  RotationBST.HeavyPath.Finger.History.state_mass valid

theorem state_side_sizes {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α} (valid : Valid weight cs left key right s) :
    s.pair.lower.decode.tree.mirror.size =
      ((Recursive.History.lower s.ancestors).flatMap Entry.lowerBlock).length + left.erase.size ∧
    s.pair.upper.decode.tree.size =
      right.erase.size + ((Recursive.History.upper s.ancestors).flatMap Entry.upperBlock).length :=
  RotationBST.HeavyPath.Finger.History.state_side_sizes valid

theorem state_size {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α} (valid : Valid weight cs left key right s) :
    s.pair.tree.size = (plug cs (.node left key right)).erase.size :=
  RotationBST.HeavyPath.Finger.History.state_size valid

theorem state_root_key {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α} (valid : Valid weight cs left key right s) :
    (Pointer.Config.mk s.pair.tree []).key? = (Config.mk (.node left key right) cs).erase.key? :=
  RotationBST.HeavyPath.Finger.History.state_root_key valid

theorem state_labels {α : Type} [Preorder α] {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α} (valid : Valid weight cs left key right s)
    (ordered : (plug cs (.node left key right)).Ordered) :
    ∃! u : LabelledTree α, u.erase = s.pair.tree ∧
      u.inorder = (plug cs (.node left key right)).inorder ∧ u.Ordered :=
  RotationBST.HeavyPath.Finger.History.state_labels valid ordered

theorem state_depth {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    {s : State α} (valid : Valid weight cs left key right s)
    {before after : List α} {target : α}
    (occurrence : (plug cs (.node left key right)).inorder = before ++ target :: after) :
    (Tree.depth s.pair.tree before.length : ℝ) ≤
      15 + 15 * Real.logb 2 (HeavyPath.mass weight (plug cs (.node left key right)) / weight target) :=
  RotationBST.HeavyPath.Finger.History.state_depth valid occurrence

theorem state_depth_at {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    {s : State α} (valid : Valid weight cs left key right s)
    (rank : Fin (plug cs (.node left key right)).inorder.length) :
    (Tree.depth s.pair.tree rank.val : ℝ) ≤
      15 + 15 * Real.logb 2 (HeavyPath.mass weight (plug cs (.node left key right)) /
        weight ((plug cs (.node left key right)).inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Finger.History.state_depth_at valid rank

theorem state_search_walk {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    {s : State α} (valid : Valid weight cs left key right s)
    (rank : Fin (plug cs (.node left key right)).inorder.length) :
    ∃ (visited : Pointer.Config) (cost : Nat),
      visited.tree = s.pair.tree ∧ visited.key? = some rank.val ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ visited cost ∧
      Pointer.Trace visited ⟨s.pair.tree, []⟩ cost ∧
      (1 + 2 * cost : ℝ) ≤ 31 + 30 * Real.logb 2
        (HeavyPath.mass weight (plug cs (.node left key right)) /
          weight ((plug cs (.node left key right)).inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Finger.History.state_search_walk valid rank

theorem build_state {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ s : State α, Valid weight cs left key right s ∧ s.pair = build weight cs left right :=
  RotationBST.HeavyPath.Finger.History.build_state positive

theorem state_initialization {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ (s : State α) (cost : Nat), Valid weight cs left key right s ∧
      Pointer.Trace ⟨(plug cs (.node left key right)).erase, []⟩ ⟨s.pair.tree, []⟩ cost ∧
      cost ≤ 16 * (plug cs (.node left key right)).erase.size :=
  RotationBST.HeavyPath.Finger.History.state_initialization positive

theorem build_state_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ s : State α, Valid weight cs left key right s ∧ s.pair = build weight cs left right ∧
      s.potential ≤ 23 * (plug cs (.node left key right)).erase.size :=
  RotationBST.HeavyPath.Finger.History.build_state_bounded positive

theorem state_initialization_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ (s : State α) (cost : Nat), Valid weight cs left key right s ∧
      Pointer.Trace ⟨(plug cs (.node left key right)).erase, []⟩ ⟨s.pair.tree, []⟩ cost ∧
      cost ≤ 16 * (plug cs (.node left key right)).erase.size ∧
      s.potential ≤ 23 * (plug cs (.node left key right)).erase.size ∧
      cost + s.potential ≤ 39 * (plug cs (.node left key right)).erase.size :=
  RotationBST.HeavyPath.Finger.History.state_initialization_bounded positive

theorem potential_bound {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α}
    (valid : Valid weight cs left key right s) :
    s.potential + 20 ≤ 20 * (plug cs (.node left key right)).erase.size :=
  RotationBST.HeavyPath.Finger.History.potential_bound valid

end RotationBST.HeavyPath.Finger.History.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Finger.History.Results`: 13 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Finger.History.Results allowing [
  RotationBST.Models.Rotation.Abstract,
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
