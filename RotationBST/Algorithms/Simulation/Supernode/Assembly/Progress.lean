module

public import RotationBST.Algorithms.Simulation.Supernode.Assembly.Attachment
public import RotationBST.Algorithms.Simulation.Supernode.Progress
public import RotationBST.Models.Region.Holes

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- An exposed region with at least one active key has strictly smaller holes. -/
theorem region_hole_smaller {region : Region} {lo : Nat}
    (active : (Region.keys region lo).Nonempty) {hole : Nat × Tree}
    (member : hole ∈ Region.holes region lo) : hole.2.size < region.tree.size := by
  cases region with
  | hole tree => exact False.elim (Finset.not_nonempty_empty active)
  | node left right =>
    simp only [Region.holes, List.mem_append] at member
    rcases member with member | member
    · have bounds := Region.holes_bounds member
      simp only [Pointer.Lazy.Skeleton.tree, Tree.size]
      omega
    · have bounds := Region.holes_bounds member
      simp only [Pointer.Lazy.Skeleton.tree, Tree.size]
      omega

/-- Entering a represented subtree exposes at least one parent key. -/
theorem selectParent_nonempty {n time request lo : Nat} {P : Finset Point} {keys : Finset Nat}
    {state : State} {children : List Nested}
    (history : History n time P) (legal : Completion n time request P keys)
    (represented : Represents P lo (.layer state children))
    (entered : (keys ∩ Finset.Ico lo (lo + (Nested.layer state children).tree.size)).Nonempty) :
    (Region.keys (selectParent state children lo keys).1.region lo).Nonempty := by
  rw [selectParent_keys represented keys]
  have canonical : Region.keys (nestedRegion state children) lo =
      supernodeKeys P lo (lo + (Nested.layer state children).tree.size) := by
    cases represented with
    | layer _ _ _ _ _ canonical _ => simpa only [Nested.tree, nestedRegion] using canonical
  rw [canonical]
  exact supernode_touched history legal entered

/-- Every recursive hole after parent selection is smaller than the original
subtree. This provides the measure for well-founded row extraction. -/
theorem selectParent_hole_smaller {n time request lo : Nat} {P : Finset Point} {keys : Finset Nat}
    {state : State} {children : List Nested}
    (history : History n time P) (legal : Completion n time request P keys)
    (represented : Represents P lo (.layer state children))
    (entered : (keys ∩ Finset.Ico lo (lo + (Nested.layer state children).tree.size)).Nonempty)
    {hole : Nat × Tree}
    (member : hole ∈ Region.holes (selectParent state children lo keys).1.region lo) :
    hole.2.size < (Nested.layer state children).tree.size := by
  have smaller := region_hole_smaller (selectParent_nonempty history legal represented entered) member
  have same := (selectParent_spec represented keys).2.1.size_eq
  omega

end RotationBST.Geometric.Online.Supernode
