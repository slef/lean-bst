module

public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Refinement.Load
public import RotationBST.Structures.TreeBuffer.Shared.Navigation

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Streaming.Refinement

/-- Restore after an arbitrary interruption. Both persistent fingers may be
away from the root. Parent moves of the worker finger are charged before
normalization; the snapshot cells are only read and remain valid afterward. -/
theorem load_interrupted (saved : Tree) (data : Nat → Nat) (stored : CellIO.Stored saved data)
    (actual : Shared.State Nat 2) (valid : actual.Valid data) (same : actual.tree.erase.size = saved.size) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ final.Valid data ∧
      final.tree.erase = saved ∧ (Pointer.Config.mk saved []).key? = some (final.position 0) ∧
      Reads data events ∧ cost ≤ 841 * saved.size := by
  obtain ⟨rooted, rootCost, navigation, rootedValid, shape, atRoot, _, _, rootBound⟩ := Shared.to_root data actual valid 0
  obtain ⟨final, events, loadCost, loading, finalValid, result, finalRoot, reads, bound⟩ :=
    load_rooted saved actual.tree.erase same data stored rooted rootedValid shape atRoot
  refine ⟨final, events, rootCost + loadCost, navigation.append loading, finalValid, result, finalRoot, reads, ?_⟩
  omega

end RotationBST.TreeBuffer.Snapshot.Streaming.Refinement
