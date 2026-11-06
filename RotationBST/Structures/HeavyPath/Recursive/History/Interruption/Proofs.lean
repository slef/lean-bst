module

public import RotationBST.Structures.HeavyPath.Recursive.History.Abstract
public import RotationBST.Bounds.StaticTree.Trace.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History.Interruption

/-- Expose a source root with one shared amortized, worst-case, and physical
prefix certificate. Every nested child history remains valid. -/
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
                10 * Real.logb 2 shape.size := by
  obtain ⟨a, b, lc, rc, cost, left, right, trace, amortized, worst⟩ :=
    History.Results.layout_expose_bounded layout
  obtain ⟨ops, length, replay⟩ := Multifinger.Replay.Results.record trace
  have budget : (ops.length : ℝ) ≤ 10 + 10 * Real.logb 2 shape.size := by simpa only [length] using worst
  refine ⟨a, b, lc, rc, ops, left, right, replay, by simpa only [length] using amortized, budget, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bound⟩ := StaticTree.Trace.Results.replay_prefix_bound replay budget cut
  refine ⟨middle, first, last, ?_⟩
  intro rank
  have original := History.Results.layout_depth_at layout rank
  have drift := bound rank.val
  change (Tree.depth middle.tree rank.val : ℝ) ≤
    Tree.depth shape rank.val + (10 + 10 * Real.logb 2 shape.size) at drift
  linarith

/-- Join two arbitrary histories without discarding the amortized bound.
The completed recursive layout bounds depth backwards across each physical
suffix, so all original keys are covered during the join. -/
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
                14 * Real.logb 2 (Tree.node a b).size := by
  obtain ⟨shape, credit, cost, joined, trace, amortized, worst⟩ :=
    History.Results.layout_join_bounded left right positive
  obtain ⟨ops, length, replay⟩ := Multifinger.Replay.Results.record trace
  have budget : (ops.length : ℝ) ≤ 10 + 14 * Real.logb 2 (Tree.node a b).size := by
    simpa only [length] using worst
  refine ⟨shape, credit, ops, joined, replay, by simpa only [length] using amortized, budget, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bounds⟩ := StaticTree.Trace.Results.replay_prefix_depth replay cut
  refine ⟨middle, first, last, ?_⟩
  intro rank
  have lastBound := (bounds rank.val).trans (min_le_right _ _)
  have lengthBound : (ops.drop cut).length ≤ ops.length := by simp
  have drift : (Tree.depth middle.tree rank.val : ℝ) ≤ Tree.depth shape rank.val + ops.length := by
    change Tree.depth middle.tree rank.val ≤
      Tree.depth shape rank.val + (ops.drop cut).length at lastBound
    exact_mod_cast (show Tree.depth middle.tree rank.val ≤ Tree.depth shape rank.val + ops.length by omega)
  have finalDepth := History.Results.layout_depth_at joined rank
  linarith

/-- Unit analysis weights give a logarithmic bound for every key throughout
source-root exposure, even with nested, noncanonical payload histories. -/
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
          (Tree.depth middle.tree rank.val : ℝ) ≤ 17 + 25 * Real.logb 2 shape.size := by
  obtain ⟨a, b, lc, rc, ops, left, right, replay, amortized, worst, prefixes⟩ := expose layout
  refine ⟨a, b, lc, rc, ops, left, right, replay, amortized, worst, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bounds⟩ := prefixes cut
  refine ⟨middle, first, last, ?_⟩
  intro rank
  have bound := bounds rank
  simp only [HeavyPath.Results.unit_mass, div_one, ← History.Results.layout_size layout] at bound
  linarith

/-- Unit-weight recursive joining is logarithmic at every physical cut. -/
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
          (Tree.depth middle.tree rank.val : ℝ) ≤ 17 + 29 * Real.logb 2 (Tree.node a b).size := by
  obtain ⟨shape, credit, ops, joined, replay, amortized, worst, prefixes⟩ := join (key := key) left right (by norm_num)
  refine ⟨shape, credit, ops, joined, replay, amortized, worst, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bounds⟩ := prefixes cut
  refine ⟨middle, first, last, ?_⟩
  intro rank
  have bound := bounds rank
  have size : (LabelledTree.node l key r).erase.size = (Tree.node a b).size := by
    simp only [LabelledTree.erase, Tree.size, History.Results.layout_size left, History.Results.layout_size right]
  simp only [HeavyPath.Results.unit_mass, div_one, size] at bound
  linarith

end RotationBST.HeavyPath.Recursive.History.Interruption
