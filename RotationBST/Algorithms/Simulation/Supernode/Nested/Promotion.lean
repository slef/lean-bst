module

public import RotationBST.Algorithms.Simulation.Supernode.Nested.Locality
public import RotationBST.Algorithms.Simulation.Supernode.Layer.Update

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- The exact child interval appears among the outer region's untouched holes. -/
theorem nested_child_hole (state : State) (children : List Nested)
    (arity : children.length = state.size + 1) (lo : Nat) (i : Fin children.length) :
    (lo + i.val + gapWeight (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 i.val,
      children[i].tree) ∈ Region.holes (nestedRegion state children) lo := by
  have bound : i.val ≤ state.tree.size := by rw [state_size]; have h := i.isLt; omega
  have member := withGaps_hole_mem state.tree (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 lo i.val bound
  simpa only [nestedRegion, Nat.zero_add, List.getElem?_map,
    List.getElem?_eq_getElem i.isLt, Option.map_some, Option.getD_some, Fin.getElem_fin] using member

/-- Promoting precisely the outer active keys preserves every represented
child, and establishes the canonical current-row supernode. -/
theorem Represents.promote {n time : Nat} {P : Finset Point} (history : History n time P)
    (lo : Nat) (state : State) (children : List Nested) (balanced : state.HeightValid)
    (arity : children.length = state.size + 1)
    (subtrees : ∀ i : Fin children.length,
      Represents P
        (lo + i.val + gapWeight (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 i.val)
        children[i]) :
    Represents (P ∪ row time (Region.keys (nestedRegion state children) lo)) lo (.layer state children) := by
  refine .layer lo state children balanced arity ?_ ?_
  · have nonempty : (Region.keys (nestedRegion state children) lo).Nonempty := by
      apply Finset.card_pos.mp
      rw [Region.keys_card]
      change 0 < (withGaps state.tree _ 0).size
      rw [withGaps_size, state_size]
      simp only [State.size]
      omega
    exact (promoted_supernode history (nestedRegion state children) lo nonempty).symm
  · intro i
    apply (subtrees i).untouched
    intro key lower upper
    exact Region.hole_disjoint (nested_child_hole state children arity lo i) lower upper

end RotationBST.Geometric.Online.Supernode
