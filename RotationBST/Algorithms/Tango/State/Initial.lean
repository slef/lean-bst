module

public import RotationBST.Algorithms.Tango.State.Potential

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Arboral.Region Pointer.Lazy.Skeleton

/-- The initial marked BST realizes precisely the initial singleton paths. -/
theorem initial_components (t : Tree) (lo : Nat) :
    (((initial t).components lo).map fun p => p.2.keys p.1) =
      ((decomposePaths t lo []).parts.map List.toFinset) := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    have ihl := il lo
    have ihr := ir (lo + l.size + 1)
    simp only [components, List.map_append] at ihl ihr
    simp only [initial, components, rootComponent, region, initial_tree, detached,
      ite_true, List.singleton_append, List.map_cons, List.map_append,
      keys, Pointer.Lazy.Skeleton.tree, Finset.union_empty, Finset.insert_empty,
      decomposePaths, labels, List.filter_nil, List.map_nil, List.getLast?_nil,
      PathDecomposition.parts, List.cons_ne_nil, ite_false, List.toFinset_cons,
      List.toFinset_nil]
    simp only [rootComponent, PathDecomposition.parts] at ihl ihr
    rw [← ihl, ← ihr]
    simp only [List.append_assoc]

theorem initial_represents (t : Tree) : Represents (initial t) t [] := by
  refine ⟨by rw [initial_tree], ?_, ?_⟩
  · rw [initial_components]
    exact List.Perm.refl _
  · cases t <;> simp [initial, region, keys, Pointer.Lazy.Skeleton.tree,
      decomposePaths, labels]

end RotationBST.Tango.MarkedTree
