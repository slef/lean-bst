module

public import RotationBST.Algorithms.Tango.State.Rebuild.Normalization
public import RotationBST.Algorithms.Tango.State.Lifting

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Arboral.Region

theorem rebuild_shape_fringe (s : MarkedTree) : rebuild (shape s.region) s.fringe = s.normalizeRoot := by
  have h := congrArg Prod.fst (fill_shape_fringe s [])
  simpa only [List.append_nil, rebuild] using h

theorem normalizeRoot_potential (s : MarkedTree) : s.normalizeRoot.potential = s.potential := by
  rw [potential_fringe, normalizeRoot_region, normalizeRoot_fringe, ← potential_fringe]

/-- Given auxiliary rotations, reconstruct their endpoint without choosing an
existential marked-tree witness. The same rotation count applies to the full BST. -/
theorem rebuild_rotations (s : MarkedTree) (target : Tree) (cost : Nat)
    (rotations : Rotations (shape s.region) target cost) :
    shape (rebuild target s.fringe).region = target ∧
      s.fringe = (rebuild target s.fringe).fringe ∧
      Rotations s.tree (rebuild target s.fringe).tree cost := by
  obtain ⟨u, hu, hf, hr⟩ := lift_rotations rotations s rfl
  have rebuilt : rebuild target s.fringe = u.normalizeRoot := by
    rw [← hu, hf, rebuild_shape_fringe]
  rw [rebuilt, normalizeRoot_region, normalizeRoot_fringe, normalizeRoot_tree]
  exact ⟨hu, hf, hr⟩

end RotationBST.Tango.MarkedTree
