module

public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Refinement.Steps
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Restoration

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Streaming.Refinement

/-- Lift an entire interleaved streaming execution, retaining both fingers in
one labelled tree and charging all routing reads and rotation maintenance. -/
theorem trace {data : Nat → Nat} {s t : State} {w p r : Nat} (run : Trace data s t w p r)
    (valid : s.Valid) (actual : Shared.State Nat 2) (represented : Represents actual s data) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ Represents final t data ∧
      Reads data events ∧ cost ≤ 4 * w + 15 * p := by
  induction run generalizing actual with
  | refl => exact ⟨actual, [], 0, .refl, represented, reads_nil data, Nat.le_refl _⟩
  | step first _ ih =>
    obtain ⟨middle, firstEvents, firstCost, realized, middleRep, firstReads, firstBound⟩ :=
      step first valid actual represented
    obtain ⟨final, lastEvents, lastCost, rest, finalRep, lastReads, lastBound⟩ :=
      ih (first.valid valid) middle middleRep
    refine ⟨final, firstEvents ++ lastEvents, firstCost + lastCost, realized.append rest,
      finalRep, reads_append firstReads lastReads, ?_⟩
    omega

/-- Streaming restoration from any represented nonempty vine has a complete
shared-node execution. The conservative constant includes every metadata
access; cells are only read and both persistent fingers remain valid. -/
theorem restore_from (saved : Tree) (data : Nat → Nat) (stored : CellIO.Stored saved data)
    (position : Nat) (present : position < saved.size) (actual : Shared.State Nat 2)
    (represented : Represents actual (initial (vine saved.size) position) data) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ final.Valid data ∧
      final.tree.erase = saved ∧ (Pointer.Config.mk saved []).key? = some (final.position 0) ∧
      Reads data events ∧ cost ≤ 780 * saved.size := by
  obtain ⟨t, w, p, r, run, _, output, _, bound⟩ := Streaming.restore_from saved data stored position present
  have valid := initial_valid (vine saved.size) position (by simpa only [vine_size] using present)
  obtain ⟨final, events, cost, actualRun, finalRep, reads, charged⟩ := trace run valid actual represented
  refine ⟨final, events, cost, actualRun, finalRep.1, ?_, ?_, reads, ?_⟩
  · simpa only [output, Pointer.Config.tree, Pointer.plug] using finalRep.2.1
  · simpa only [output] using finalRep.2.2.1
  · omega

end RotationBST.TreeBuffer.Snapshot.Streaming.Refinement
