module

public import RotationBST.Algorithms.Tango.State.Preservation
public import RotationBST.Algorithms.Tango.Auxiliary.Execution
public import RotationBST.Algorithms.Tango.State.Splay.Proofs

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Arboral.Region

theorem represents_of_fringe {s t : MarkedTree} {reference : Tree} {past : List Nat}
    (represented : Represents s reference past) (same : s.fringe = t.fringe) :
    Represents t reference past := by
  have hfr : s.region.fringe = t.region.fringe := by rw [← fringe_tree, ← fringe_tree, same]
  have sizes := (same_of_fringe hfr 0).1
  simp only [region_tree] at sizes
  refine ⟨sizes ▸ represented.1, component_keys_eq same 0 ▸ represented.2.1, ?_⟩
  exact (same_of_fringe hfr 0).2.1.symm.trans represented.2.2

/-- Splaying the computed active rank visits the corresponding absolute key. -/
theorem splayRoot_key (s : MarkedTree) (x : Nat) (valid : x ∈ s.region.keys 0) :
    Access s.tree (s.splayRoot (index s.region 0 x)).1.tree x
      (s.splayRoot (index s.region 0 x)).2 := by
  let k := index s.region 0 x
  have vk : k < s.region.size := index_valid valid
  obtain ⟨hf, _, _, _⟩ := splayRoot_spec s k vk
  have hrun := (Splay.run_correct (shape s.region) k (by rwa [shape_size])).1
  have rebuilt := rebuild_rotations s _ _ hrun.1
  have correct := auxiliaryRun_correct s.region k vk
  have equal : (s.splayRoot k).1.region = (auxiliaryRun s.region k).1 := by
    apply shape_fringe_injective (rebuilt.1.trans correct.1.symm)
    have hfr : s.region.fringe = (s.splayRoot k).1.region.fringe := by
      rw [← fringe_tree, ← fringe_tree, hf]
    exact hfr.symm.trans correct.2.1
  have served := auxiliaryRun_access s.region x valid
  change Access s.region.tree (auxiliaryRun s.region k).1.tree x (Splay.run (shape s.region) k).2 at served
  rw [← equal, region_tree, region_tree] at served
  exact served

/-- Splay a key of the root component in the actual marked BST. The bound uses
the global potential of all components, and the component partition is unchanged. -/
theorem access (s : MarkedTree) (x : Nat) (valid : x ∈ s.region.keys 0) :
    ∃ u : MarkedTree, ∃ cost : Nat, s.fringe = u.fringe ∧ Access s.tree u.tree x cost ∧
      (cost : ℝ) + u.potential - s.potential ≤ 3 * Real.logb 2 s.region.size + 1 := by
  obtain ⟨fringe, _, _, bound⟩ := splayRoot_spec s _ (index_valid valid)
  exact ⟨_, _, fringe, splayRoot_key s x valid, bound⟩

end RotationBST.Tango.MarkedTree
