module

public import RotationBST.Structures.PopTart.Cherry.Depth
public import RotationBST.Structures.PopTart.Height
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Cherry
open WeightedTree

/-- The outer leaf-depth theorem bounds every actual key when all fringe
slots are empty, giving the ordinary Cherry BST height bound. -/
theorem key_depth {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom) (empty : (layers.decode bottom).EmptyFringe)
    (x : Nat) (inside : x < (layers.decode bottom).tree.size) :
    (Tree.depth (layers.decode bottom).tree x : ℝ) <
      4 * Real.logb 2 (((layers.decode bottom).tree.size + 1 : Nat) : ℝ) := by
  obtain ⟨subtree, weight, depth, slot, equal⟩ := height_slot (layers.decode bottom)
  have bound := depth_log valid base slot
  rw [equal, empty_count empty] at bound
  have above : (Tree.depth (layers.decode bottom).tree x : ℝ) < (layers.decode bottom).height := by
    exact_mod_cast key_depth_lt_height empty x inside
  exact above.trans_le bound

end RotationBST.PopTart.Cherry
