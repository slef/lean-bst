module

public import RotationBST.Bounds.LazyFinger.ReadonlyWalk

@[expose] public section
namespace RotationBST.LazyFinger

/-- The lazy-finger distance is realized by a legal persistent-pointer walk
between the two keys of the same reference tree. -/
theorem pointer_walk (t : Tree) (x y : Nat) (hx : x < t.size) (hy : y < t.size) :
    ∃ a b : Pointer.Config, a.tree = t ∧ b.tree = t ∧ a.key? = some x ∧ b.key? = some y ∧
      Pointer.Trace a b (distance t x y) := by
  obtain ⟨a, b, treeA, treeB, keyA, keyB, walk⟩ := readonly_walk t x y hx hy
  exact ⟨a, b, treeA, treeB, keyA, keyB, walk.trace⟩

end RotationBST.LazyFinger
