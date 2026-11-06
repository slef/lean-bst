module

public import RotationBST.Structures.PopTart.Chocolate.Depth
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

private theorem unit_mass (t : WeightedTree)
    (unitWeights : ∀ subtree weight depth, SlotAt t subtree weight depth → weight = 1) :
    t.mass = (t.leafCount : ℝ) := by
  induction t with
  | leaf subtree weight =>
    have one := unitWeights subtree weight 0 (.leaf _ _)
    simpa only [mass, leafCount, Nat.cast_one] using one
  | node l r ihL ihR =>
    have left := ihL (fun _ _ _ slot => unitWeights _ _ _ (.left slot))
    have right := ihR (fun _ _ _ slot => unitWeights _ _ _ (.right slot))
    simp only [mass, leafCount, Nat.cast_add, left, right]

/-- Unit weights give logarithmic outer height, with no restriction on frozen
icing history or on the positions of the original fringe occurrences. -/
theorem uniform_height {stack : Layer} (valid : stack.Valid 0)
    (unitWeights : ∀ subtree weight depth, SlotAt stack.decode subtree weight depth → weight = 1) :
    (stack.decode.height : ℝ) ≤ 7 + 7 * Real.logb 2 (stack.decode.leafCount) := by
  obtain ⟨subtree, weight, depth, slot, same⟩ := height_slot stack.decode
  have one := unitWeights subtree weight depth slot
  have bound := weighted_depth valid slot (by rw [one]; norm_num)
  simpa only [one, same, div_one, unit_mass stack.decode unitWeights] using bound

/-- When the fringe payloads are empty, the height estimate also bounds the
search depth of every actual BST key. -/
theorem uniform_key_depth {stack : Layer} (valid : stack.Valid 0)
    (unitWeights : ∀ subtree weight depth, SlotAt stack.decode subtree weight depth → weight = 1)
    (empty : stack.decode.EmptyFringe) (x : Nat) (inside : x < stack.decode.tree.size) :
    (Tree.depth stack.decode.tree x : ℝ) <
      7 + 7 * Real.logb 2 (((stack.decode.tree.size + 1 : Nat) : ℝ)) := by
  have key : (Tree.depth stack.decode.tree x : ℝ) < (stack.decode.height : ℝ) := by
    exact_mod_cast key_depth_lt_height empty x inside
  have bound := uniform_height valid unitWeights
  rw [empty_count empty] at bound
  exact key.trans_le bound

end RotationBST.PopTart.Chocolate
