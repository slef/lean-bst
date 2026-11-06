module

public import RotationBST.Structures.HeavyPath.Finger.Transfer.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Paired.Population.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Top.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Population
open PopTart PopTart.Chocolate

/-- Opaque payloads can only increase the whole tree's population. -/
theorem pair_population (p : Pair) :
    1 ≤ p.lower.decode.leafCount ∧ p.lower.decode.leafCount ≤ p.tree.size ∧
    1 ≤ p.upper.decode.leafCount ∧ p.upper.decode.leafCount ≤ p.tree.size := by
  have lower := Paired.Population.Results.leaf_count_size p.lower.decode
  have upper := Paired.Population.Results.leaf_count_size p.upper.decode
  simp only [Pair.tree, Tree.size, Tree.mirror_size]
  omega

private theorem lower_log (p : Pair) :
    Real.logb 2 (p.lower.decode.leafCount) ≤ Real.logb 2 p.tree.size := by
  have population := pair_population p
  apply Real.logb_le_logb_of_le (by norm_num)
  · exact_mod_cast (show 0 < p.lower.decode.leafCount by omega)
  · exact_mod_cast population.2.1

private theorem upper_log (p : Pair) :
    Real.logb 2 (p.upper.decode.leafCount) ≤ Real.logb 2 p.tree.size := by
  have population := pair_population p
  apply Real.logb_le_logb_of_le (by norm_num)
  · exact_mod_cast (show 0 < p.upper.decode.leafCount by omega)
  · exact_mod_cast population.2.2.2

theorem lower_push {p : Pair} (valid : p.Valid) :
    (p.lower.pushCost : ℝ) ≤ 6 + 14 * Real.logb 2 p.tree.size := by
  have worst := Chocolate.Results.push_worst_case valid.1
  have logarithm := lower_log p
  linarith

theorem upper_push {p : Pair} (valid : p.Valid) :
    (p.upper.pushCost : ℝ) ≤ 6 + 14 * Real.logb 2 p.tree.size := by
  have worst := Chocolate.Results.push_worst_case valid.2
  have logarithm := upper_log p
  linarith

theorem lower_pop {p : Pair} (valid : p.Valid) :
    (p.lower.popCost : ℝ) ≤ 6 + 10 * Real.logb 2 p.tree.size := by
  have worst := Chocolate.Results.pop_worst_case valid.1
  have logarithm := lower_log p
  linarith

theorem upper_pop {p : Pair} (valid : p.Valid) :
    (p.upper.popCost : ℝ) ≤ 6 + 10 * Real.logb 2 p.tree.size := by
  have worst := Chocolate.Results.pop_worst_case valid.2
  have logarithm := upper_log p
  linarith

private theorem top_size (stack : Layer) : stack.top.tree.size ≤ stack.decode.tree.size := by
  rw [Chocolate.Top.Results.decode_top]
  cases stack.topTail <;> simp [WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.size]
  omega

theorem lower_payload_size {p : Pair} {shape : Tree} {charge : ℝ}
    (stored : p.lower.top = .leaf shape.mirror charge) : shape.size ≤ p.tree.size := by
  have size := top_size p.lower
  simp only [stored, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree,
    Tree.mirror_size] at size
  change shape.size ≤ p.lower.decode.tree.size at size
  simp only [Pair.tree, Tree.size, Tree.mirror_size]
  omega

theorem upper_payload_size {p : Pair} {shape : Tree} {charge : ℝ}
    (stored : p.upper.top = .leaf shape charge) : shape.size ≤ p.tree.size := by
  have size := top_size p.upper
  simp only [stored, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree] at size
  change shape.size ≤ p.upper.decode.tree.size at size
  simp only [Pair.tree, Tree.size]
  omega

end RotationBST.HeavyPath.Finger.Population
