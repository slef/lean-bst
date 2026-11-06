module

public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Refinement.Traces
public import RotationBST.Structures.TreeBuffer.Shared.Replay
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Load

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Streaming.Refinement

/-- Rooted loading does not require the inactive scan finger to point to the
root. Its existing node identity is carried through normalization and used
as the starting point of the charged streaming scan. -/
theorem load_rooted (saved current : Tree) (same : current.size = saved.size)
    (data : Nat → Nat) (stored : CellIO.Stored saved data) (actual : Shared.State Nat 2)
    (valid : actual.Valid data) (tree : actual.tree.erase = current)
    (root : (Pointer.Config.mk current []).key? = some (actual.position 0)) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ final.Valid data ∧
      final.tree.erase = saved ∧ (Pointer.Config.mk saved []).key? = some (final.position 0) ∧
      Reads data events ∧ cost ≤ 840 * current.size := by
  obtain ⟨middle, normalCost, normalization, shape, replayKey, inactive, normalBound⟩ :=
    Shared.replay (record current) data actual valid 0 ⟨current, []⟩ ⟨vine current.size, []⟩
      tree root (Controller.normalization current).replay
  have represented : Represents middle (initial (vine saved.size) (actual.position 1)) data := by
    refine ⟨normalization.valid data valid, ?_, ?_, inactive 1 (by decide)⟩
    · simpa only [same, Pointer.Config.tree, Pointer.plug, initial] using shape
    · simpa only [same, initial] using replayKey
  have present : actual.position 1 < saved.size := by simpa only [tree, same] using valid.2.2 1
  obtain ⟨final, events, restoreCost, restoration, finalValid, result, finalRoot, reads, bound⟩ :=
    restore_from saved data stored (actual.position 1) present middle represented
  refine ⟨final, events, normalCost + restoreCost, normalization.append restoration,
    finalValid, result, finalRoot, reads, ?_⟩
  have length := record_length current
  omega

/-- Complete nonempty loading from an already represented tree. Normalization
preserves the inactive buffer finger and all cells; restoration then includes
every routing read and rotation update. The bound excludes initial field setup. -/
theorem load (saved current : Tree) (_nonempty : current ≠ .nil) (same : current.size = saved.size)
    (data : Nat → Nat) (stored : CellIO.Stored saved data) (actual : Shared.State Nat 2)
    (valid : actual.Valid data) (tree : actual.tree.erase = current)
    (root : (Pointer.Config.mk current []).key? = some (actual.position 0))
    (_buffer : actual.position 1 = rootPosition current) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ final.Valid data ∧
      final.tree.erase = saved ∧ (Pointer.Config.mk saved []).key? = some (final.position 0) ∧
      Reads data events ∧ cost ≤ 840 * current.size :=
  load_rooted saved current same data stored actual valid tree root

end RotationBST.TreeBuffer.Snapshot.Streaming.Refinement
