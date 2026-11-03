module

public import RotationBST.Algorithms.Simulation.Supernode.Nested.Defs
public import RotationBST.Algorithms.Simulation.Supernode.Layer.Proofs
public import RotationBST.Algorithms.Simulation.Supernode.Embedding.Holes
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Proofs

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- The finite child list supplies every gap exactly once; no default tree is
used in a well-formed layer. -/
theorem nestedRegion_gap_heap {P : Finset Point} {lo : Nat} {state : State} {children : List Nested}
    (arity : children.length = state.size + 1)
    (heaps : ∀ i : Fin children.length,
      Heap (fun key => OrderDual.toDual (lastTouch P key)) children[i].tree
        (lo + i.val + gapWeight (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 i.val)) :
    ∀ hole ∈ Region.holes (nestedRegion state children) lo,
      Heap (fun key => OrderDual.toDual (lastTouch P key)) hole.2 hole.1 := by
  intro hole member
  obtain ⟨i, bound, equal⟩ := withGaps_hole state.tree _ 0 lo member
  have inside : i < children.length := by rw [state_size] at bound; omega
  subst hole
  have result := heaps ⟨i, inside⟩
  simpa only [Nat.zero_add, List.getElem?_map, List.getElem?_eq_getElem inside,
    Option.map_some, Option.getD_some, Fin.getElem_fin] using result

/-- The nested representation realizes a last-touch heap on all ordinary BST
keys, not merely the keys belonging to its outermost supernode. -/
theorem Represents.heap {P : Finset Point} {lo : Nat} {state : Nested} (valid : Represents P lo state) :
    Heap (fun key => OrderDual.toDual (lastTouch P key)) state.tree lo := by
  induction valid with
  | empty lo => simp [Nested.tree, Heap]
  | layer lo state children balanced arity canonical subtrees ih =>
    simpa only [Nested.tree, nestedRegion] using (Layer.canonical canonical (nestedRegion_gap_heap arity ih)).heap

end RotationBST.Arboral.Online.Supernode
