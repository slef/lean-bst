module

public import RotationBST.Classical.Static.Balanced
public import RotationBST.Models.Rotation.Shapes
import Mathlib.Tactic

@[expose] public section

/-! Height: the balanced tree has the minimum height `⌊log₂ n⌋ + 1`. -/
namespace RotationBST.Classical.Static
open _root_.RotationBST.Tree (height balanced)

/-- Every nonempty tree has height at least `⌊log₂ n⌋ + 1`. -/
theorem log2_add_one_le_height (t : Tree) (h : 0 < t.size) : Nat.log2 t.size + 1 ≤ height t := by
  obtain ⟨x, hx, hd⟩ := exists_deep t h
  have := Tree.depth_lt_height t x hx
  omega

theorem balanced_height_eq (n : Nat) (h : 0 < n) : height (balanced n) = Nat.log2 n + 1 := by
  apply le_antisymm
  · exact Tree.balanced_height n
  · have := log2_add_one_le_height (balanced n) (by rwa [Tree.balanced_size])
    rwa [Tree.balanced_size] at this

end RotationBST.Classical.Static
