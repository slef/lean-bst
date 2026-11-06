module

public import RotationBST.Structures.HeavyPath.Recursive.History.Interruption.Proofs
public import RotationBST.Structures.HeavyPath.Recursive.History.Interruption.Initial
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History.Interruption

/-- Source-root exposure keeps its amortized and worst-case costs while every
physical prefix has a purely weighted depth bound. -/
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
              weight ((LabelledTree.node l key r).inorder[rank.val]'rank.isLt)) := by
  obtain ⟨a, b, lc, rc, cost, left, right, trace, amortized, worst⟩ :=
    History.Results.layout_expose_within layout
  obtain ⟨ops, length, replay, prefixes⟩ := trace.record
  refine ⟨a, b, lc, rc, ops, left, right, replay, by simpa only [length] using amortized,
    by simpa only [length] using worst, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bounds⟩ := prefixes cut
  refine ⟨middle, first, last, ?_⟩
  intro rank
  have initial := History.Results.layout_depth_at layout rank
  have structural := bounds.2 rank.val
  have drift : (Tree.depth middle.tree rank.val : ℝ) ≤ 4 * Tree.depth shape rank.val + 10 := by
    exact_mod_cast structural
  linarith

/-- Joining two arbitrary layouts has the same cost accounting and a weighted
prefix certificate measured against the original source subtree. -/
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
              weight ((LabelledTree.node l key r).inorder[rank.val]'rank.isLt)) := by
  obtain ⟨shape, credit, cost, joined, trace, amortized, worst⟩ :=
    History.Results.layout_join_within left right positive
  obtain ⟨ops, length, replay, prefixes⟩ := trace.record
  refine ⟨shape, credit, ops, joined, replay, by simpa only [length] using amortized,
    by simpa only [length] using worst, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bounds⟩ := prefixes cut
  refine ⟨middle, first, last, ?_⟩
  intro rank
  have initial := node_depth_at left right positive rank
  have structural := bounds.2 rank.val
  have drift : (Tree.depth middle.tree rank.val : ℝ) ≤
      4 * Tree.depth (.node a b) rank.val + 16 := by exact_mod_cast structural
  linarith

end RotationBST.HeavyPath.Recursive.History.Interruption
