module

public import RotationBST.Structures.PopTart.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.WeightedTree

theorem perfect_count {level : Nat} {crumb : WeightedTree} (perfect : Perfect level crumb) :
    leafCount crumb = 2 ^ level := by
  induction perfect with
  | leaf => rfl
  | node left right ihL ihR => simp only [leafCount, ihL, ihR, pow_succ]; omega

theorem perfect_depth {level : Nat} {crumb : WeightedTree} (perfect : Perfect level crumb)
    {subtree : Tree} {weight : ℝ} {depth : Nat} (slot : WeightedTree.SlotAt crumb subtree weight depth) :
    depth = level := by
  induction perfect generalizing depth with
  | leaf => cases slot; rfl
  | node left right ihL ihR =>
    cases slot with
    | left found => exact congrArg (· + 1) (ihL found)
    | right found => exact congrArg (· + 1) (ihR found)

theorem height_slot (t : WeightedTree) :
    ∃ subtree weight depth, SlotAt t subtree weight depth ∧ depth = t.height := by
  induction t with
  | leaf subtree weight => exact ⟨subtree, weight, 0, .leaf _ _, rfl⟩
  | node l r ihL ihR =>
    by_cases left : l.height ≤ r.height
    · obtain ⟨subtree, weight, depth, slot, same⟩ := ihR
      exact ⟨subtree, weight, depth + 1, .right slot, by simp only [height, Nat.max_eq_right left, same]⟩
    · obtain ⟨subtree, weight, depth, slot, same⟩ := ihL
      exact ⟨subtree, weight, depth + 1, .left slot, by simp only [height, Nat.max_eq_left (by omega : r.height ≤ l.height), same]⟩

theorem empty_count {t : WeightedTree} (empty : t.EmptyFringe) : leafCount t = t.tree.size + 1 := by
  induction t with
  | leaf subtree weight =>
    change subtree = .nil at empty
    subst subtree
    rfl
  | node l r ihL ihR =>
    have left := ihL empty.1
    have right := ihR empty.2
    change leafCount l + leafCount r = l.tree.size + 1 + r.tree.size + 1
    omega

/-- With empty external fringes, every actual key is strictly above the
maximum external-leaf depth. -/
theorem key_depth_lt_height {t : WeightedTree} (empty : t.EmptyFringe) (x : Nat) (valid : x < t.tree.size) :
    Tree.depth t.tree x < t.height := by
  induction t generalizing x with
  | leaf subtree weight =>
    change subtree = .nil at empty
    subst subtree
    change x < 0 at valid
    omega
  | node l r ihL ihR =>
    change x < l.tree.size + 1 + r.tree.size at valid
    change Tree.depth (.node l.tree r.tree) x < max l.height r.height + 1
    by_cases left : x < l.tree.size
    · have bound := ihL empty.1 x left
      simp only [Tree.depth, left, ite_true]
      omega
    · by_cases root : x = l.tree.size
      · subst x
        simp [Tree.depth]
      · have inside : x - l.tree.size - 1 < r.tree.size := by omega
        have bound := ihR empty.2 (x - l.tree.size - 1) inside
        simp only [Tree.depth, left, root, ite_false]
        omega

end RotationBST.PopTart.WeightedTree
