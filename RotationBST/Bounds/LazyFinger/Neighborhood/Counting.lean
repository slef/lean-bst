module

public import RotationBST.Bounds.LazyFinger.Neighborhood.Definitions.Abstract
public import RotationBST.Bounds.LazyFinger.PointerWalk
public import RotationBST.Models.Multifinger.Program.Counting

@[expose] public section
namespace RotationBST.LazyFinger

/-- A ball of radius `r` contains at most exponentially many keys, uniformly
in the tree shape, the universe size, and the starting key. -/
theorem ball_card (t : Tree) (x r : Nat) (valid : x < t.size) :
    (ball t x r).card ≤ 7 ^ r := by
  obtain ⟨source, tree, key, _, _⟩ := Pointer.search_walk t x valid
  apply Pointer.reachable_keys_card source r
  intro y member
  obtain ⟨hy, short⟩ := Finset.mem_filter.mp member
  have hy' := Finset.mem_range.mp hy
  obtain ⟨a, b, treeA, _, keyA, keyB, trace⟩ := pointer_walk t x y valid hy'
  have same : source = a := Pointer.Config.ext_key (tree.trans treeA.symm) key keyA
  exact ⟨b, distance t x y, same ▸ trace, short, keyB⟩

end RotationBST.LazyFinger
