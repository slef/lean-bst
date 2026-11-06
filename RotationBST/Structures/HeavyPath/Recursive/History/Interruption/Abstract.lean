module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Recursive.History.Interruption.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History.Interruption.Results

theorem expose {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {key : α}
    {shape : Tree} {credit : Nat} (layout : Layout weight (.node l key r) shape credit) :
    ∃ (a b : Tree) (lc rc : Nat) (ops : List Multifinger.Opcode),
      Layout weight l a lc ∧ Layout weight r b rc ∧
      Multifinger.replay ops ⟨shape, []⟩ = some ⟨.node a b, []⟩ ∧
      ops.length + lc + rc ≤ 24 + credit ∧
      (ops.length : ℝ) ≤ 10 + 10 * Real.logb 2 shape.size ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨shape, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node a b, []⟩ ∧
        ∀ rank : Fin (LabelledTree.node l key r).inorder.length,
          (Tree.depth middle.tree rank.val : ℝ) ≤
            17 + 15 * Real.logb 2 (mass weight (.node l key r) /
              weight ((LabelledTree.node l key r).inorder[rank.val]'rank.isLt)) +
                10 * Real.logb 2 shape.size :=
  RotationBST.HeavyPath.Recursive.History.Interruption.expose layout

theorem join {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {key : α}
    {a b : Tree} {lc rc : Nat} (left : Layout weight l a lc) (right : Layout weight r b rc)
    (positive : 0 < weight key) :
    ∃ (shape : Tree) (credit : Nat) (ops : List Multifinger.Opcode),
      Layout weight (.node l key r) shape credit ∧
      Multifinger.replay ops ⟨.node a b, []⟩ = some ⟨shape, []⟩ ∧
      ops.length + credit ≤ 24 + lc + rc ∧
      (ops.length : ℝ) ≤ 10 + 14 * Real.logb 2 (Tree.node a b).size ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node a b, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨shape, []⟩ ∧
        ∀ rank : Fin (LabelledTree.node l key r).inorder.length,
          (Tree.depth middle.tree rank.val : ℝ) ≤
            17 + 15 * Real.logb 2 (mass weight (.node l key r) /
              weight ((LabelledTree.node l key r).inorder[rank.val]'rank.isLt)) +
                14 * Real.logb 2 (Tree.node a b).size :=
  RotationBST.HeavyPath.Recursive.History.Interruption.join left right positive

theorem expose_uniform {α : Type} {l r : LabelledTree α} {key : α}
    {shape : Tree} {credit : Nat} (layout : Layout (fun _ => 1) (.node l key r) shape credit) :
    ∃ (a b : Tree) (lc rc : Nat) (ops : List Multifinger.Opcode),
      Layout (fun _ => 1) l a lc ∧ Layout (fun _ => 1) r b rc ∧
      Multifinger.replay ops ⟨shape, []⟩ = some ⟨.node a b, []⟩ ∧
      ops.length + lc + rc ≤ 24 + credit ∧
      (ops.length : ℝ) ≤ 10 + 10 * Real.logb 2 shape.size ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨shape, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node a b, []⟩ ∧
        ∀ rank : Fin (LabelledTree.node l key r).inorder.length,
          (Tree.depth middle.tree rank.val : ℝ) ≤ 17 + 25 * Real.logb 2 shape.size :=
  RotationBST.HeavyPath.Recursive.History.Interruption.expose_uniform layout

theorem join_uniform {α : Type} {l r : LabelledTree α} {key : α}
    {a b : Tree} {lc rc : Nat} (left : Layout (fun _ => 1) l a lc) (right : Layout (fun _ => 1) r b rc) :
    ∃ (shape : Tree) (credit : Nat) (ops : List Multifinger.Opcode),
      Layout (fun _ => 1) (.node l key r) shape credit ∧
      Multifinger.replay ops ⟨.node a b, []⟩ = some ⟨shape, []⟩ ∧
      ops.length + credit ≤ 24 + lc + rc ∧
      (ops.length : ℝ) ≤ 10 + 14 * Real.logb 2 (Tree.node a b).size ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node a b, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨shape, []⟩ ∧
        ∀ rank : Fin (LabelledTree.node l key r).inorder.length,
          (Tree.depth middle.tree rank.val : ℝ) ≤ 17 + 29 * Real.logb 2 (Tree.node a b).size :=
  RotationBST.HeavyPath.Recursive.History.Interruption.join_uniform left right

theorem node_depth_at {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {key : α}
    {a b : Tree} {lc rc : Nat} (left : Layout weight l a lc) (right : Layout weight r b rc)
    (positive : 0 < weight key) (rank : Fin (LabelledTree.node l key r).inorder.length) :
    (Tree.depth (.node a b) rank.val : ℝ) ≤
      8 + 15 * Real.logb 2 (mass weight (.node l key r) /
        weight ((LabelledTree.node l key r).inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Recursive.History.Interruption.node_depth_at left right positive rank

theorem expose_weighted {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {key : α}
    {shape : Tree} {credit : Nat} (layout : Layout weight (.node l key r) shape credit) :
    ∃ (a b : Tree) (lc rc : Nat) (ops : List Multifinger.Opcode),
      Layout weight l a lc ∧ Layout weight r b rc ∧
      Multifinger.replay ops ⟨shape, []⟩ = some ⟨.node a b, []⟩ ∧
      ops.length + lc + rc ≤ 24 + credit ∧
      (ops.length : ℝ) ≤ 10 + 10 * Real.logb 2 shape.size ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨shape, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node a b, []⟩ ∧
        ∀ rank : Fin (LabelledTree.node l key r).inorder.length,
          (Tree.depth middle.tree rank.val : ℝ) ≤
            38 + 60 * Real.logb 2 (mass weight (.node l key r) /
              weight ((LabelledTree.node l key r).inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Recursive.History.Interruption.expose_weighted layout

theorem join_weighted {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {key : α}
    {a b : Tree} {lc rc : Nat} (left : Layout weight l a lc) (right : Layout weight r b rc)
    (positive : 0 < weight key) :
    ∃ (shape : Tree) (credit : Nat) (ops : List Multifinger.Opcode),
      Layout weight (.node l key r) shape credit ∧
      Multifinger.replay ops ⟨.node a b, []⟩ = some ⟨shape, []⟩ ∧
      ops.length + credit ≤ 24 + lc + rc ∧
      (ops.length : ℝ) ≤ 10 + 14 * Real.logb 2 (Tree.node a b).size ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node a b, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨shape, []⟩ ∧
        ∀ rank : Fin (LabelledTree.node l key r).inorder.length,
          (Tree.depth middle.tree rank.val : ℝ) ≤
            48 + 60 * Real.logb 2 (mass weight (.node l key r) /
              weight ((LabelledTree.node l key r).inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Recursive.History.Interruption.join_weighted left right positive

end RotationBST.HeavyPath.Recursive.History.Interruption.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Recursive.History.Interruption.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Recursive.History.Interruption.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.History.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract]
