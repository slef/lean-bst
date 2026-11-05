module

public import RotationBST.Bounds.LazyFinger.Geometry
public import RotationBST.Models.Pointer.Walk.Basic

@[expose] public section
namespace RotationBST.LazyFinger

/-- The lazy-finger distance is realized by navigation without any rotations
between the two keys of the same reference tree. -/
theorem readonly_walk (t : Tree) (x y : Nat) (hx : x < t.size) (hy : y < t.size) :
    ∃ a b : Pointer.Config, a.tree = t ∧ b.tree = t ∧ a.key? = some x ∧ b.key? = some y ∧
      Pointer.Walk a b (distance t x y) := by
  induction t generalizing x y with
  | nil => simp [Tree.size] at hx
  | node l r il ir =>
    by_cases left : x < l.size ∧ y < l.size
    · obtain ⟨a, b, treeA, treeB, keyA, keyB, trace⟩ := il x y left.1 left.2
      refine ⟨a.under [.left r], b.under [.left r], ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Pointer.Config.under_tree, treeA, Pointer.plug]
      · simp only [Pointer.Config.under_tree, treeB, Pointer.plug]
      · simpa only [Pointer.offset, Nat.zero_add] using a.under_key [.left r] x keyA
      · simpa only [Pointer.offset, Nat.zero_add] using b.under_key [.left r] y keyB
      · simpa only [distance, left, and_self, ↓reduceIte] using trace.under [.left r]
    · by_cases right : l.size < x ∧ l.size < y
      · have xr : x - l.size - 1 < r.size := by simp only [Tree.size] at hx; omega
        have yr : y - l.size - 1 < r.size := by simp only [Tree.size] at hy; omega
        obtain ⟨a, b, treeA, treeB, keyA, keyB, trace⟩ := ir _ _ xr yr
        refine ⟨a.under [.right l], b.under [.right l], ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Pointer.Config.under_tree, treeA, Pointer.plug]
        · simp only [Pointer.Config.under_tree, treeB, Pointer.plug]
        · have shifted := a.under_key [.right l] _ keyA
          have index : Pointer.offset [.right l] + (x - l.size - 1) = x := by simp only [Pointer.offset]; omega
          simpa only [index] using shifted
        · have shifted := b.under_key [.right l] _ keyB
          have index : Pointer.offset [.right l] + (y - l.size - 1) = y := by simp only [Pointer.offset]; omega
          simpa only [index] using shifted
        · simpa only [distance, left, right, and_self, ↓reduceIte] using trace.under [.right l]
      · obtain ⟨a, treeA, keyA, _, up⟩ := Pointer.search_readonly (.node l r) x hx
        obtain ⟨b, treeB, keyB, down, _⟩ := Pointer.search_readonly (.node l r) y hy
        exact ⟨a, b, treeA, treeB, keyA, keyB, by
          simpa only [distance, left, right, ↓reduceIte] using up.append down⟩

end RotationBST.LazyFinger
