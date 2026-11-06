module

public import RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Streaming.Refinement

/-- The two persistent fingers are replay (0) and buffer scan (1). Both refer
to the same labelled nodes throughout reads, writes, and maintained rotations. -/
def Represents (actual : Shared.State Nat 2) (model : State) (data : Nat → Nat) : Prop :=
  actual.Valid data ∧ actual.tree.erase = model.cursor.tree ∧
  model.cursor.key? = some (actual.position 0) ∧ actual.position 1 = model.scan.position

/-- Restoration observes only correct reads; it never rewrites saved cells. -/
def Reads (data : Nat → Nat) (events : List (Cells.Event Nat)) : Prop :=
  ∀ event ∈ events, ∃ key, event = .read key (data key)

end RotationBST.TreeBuffer.Snapshot.Streaming.Refinement
