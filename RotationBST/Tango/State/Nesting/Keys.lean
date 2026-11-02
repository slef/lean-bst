module

public import RotationBST.Tango.State.Nesting.Offsets
public import RotationBST.Arboral.Treap.Regions.FringeSizes

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Equal component nesting fixes the absolute active keys at the root. -/
theorem nesting_keys_eq {s t : MarkedTree} (same : s.nesting = t.nesting) (lo : Nat) :
    s.region.keys lo = t.region.keys lo := by
  have aligned := (nesting_fringe_matching same).imp (fun _ _ h => nesting_size_eq h)
  have mapped : List.Forall₂ Eq (s.fringe.map (fun a => a.tree.size)) (t.fringe.map (fun b => b.tree.size)) := by
    simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using aligned
  have sizes : s.fringe.map (fun a => a.tree.size) = t.fringe.map (fun b => b.tree.size) := by
    simpa only [List.forall₂_eq_eq_eq] using mapped
  apply Arboral.Region.keys_of_fringe_sizes
  rw [← fringe_tree, ← fringe_tree, List.map_map, List.map_map]
  exact sizes

end RotationBST.Tango.MarkedTree
