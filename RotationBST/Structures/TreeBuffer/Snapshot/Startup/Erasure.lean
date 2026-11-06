module

public import RotationBST.Structures.TreeBuffer.Snapshot.Startup.Operations
public import RotationBST.Structures.TreeBuffer.Shared.Erasure.Traces

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Startup

/-- Metadata initialization leaves the original tree and all-root cursor
positions unchanged. The subsequent snapshot work projects to a real
multifinger trace, with its actual final positions and no larger cost. -/
theorem Execution.erase {tree : Tree} {n : Nat} {fields : Nat → IntervalMetadata.Bounds}
    {data : Nat → Nat} {final : Shared.State Nat 2} {events : List (Cells.Event Nat)} {cost : Nat}
    (run : Execution tree n fields data final events cost) (size : n = tree.size) (nonempty : tree ≠ .nil) :
    ∃ touches, Multifinger.Trace (Multifinger.initial 2 tree) touches final.erase ∧ touches.length ≤ cost := by
  obtain ⟨ready, setupCost, work, computed, _, _, _, trace, rfl⟩ := run
  obtain ⟨expected, expectedCost, canonical, _, _, cursor, _, _⟩ := Nodes.Initialization.complete tree n size fields data
  obtain ⟨rfl, rfl⟩ := Option.some.inj (computed.symm.trans canonical)
  rw [cursor] at trace
  let actual : Shared.State Nat 2 := ⟨Nodes.label data tree 0, fun _ => Streaming.rootPosition tree⟩
  have valid : actual.Valid data := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [actual, Nodes.label_routing, Nodes.label_erase]
    · simp only [actual, Nodes.label_payload, Nodes.label_erase]
    · intro i
      simpa only [actual, Nodes.label_erase] using Streaming.rootPosition_valid tree nonempty
  have shared : Shared.Trace actual final events work := by
    simpa only [actual, LabelledCursor.Config.tree, LabelledCursor.plug] using trace
  obtain ⟨touches, erased, bound⟩ := shared.erase data valid
  refine ⟨touches, ?_, by omega⟩
  cases tree <;>
    simpa only [actual, Shared.State.erase, Nodes.label_erase, Multifinger.initial, Streaming.rootPosition,
      Pointer.Config.key?, Pointer.offset, Nat.zero_add, Option.getD_none, Option.getD_some] using erased

end RotationBST.TreeBuffer.Snapshot.Startup
