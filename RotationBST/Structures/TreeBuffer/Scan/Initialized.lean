module

public import RotationBST.Structures.TreeBuffer.Scan.Progress
public import RotationBST.Models.Labelled.Intervals.Initialization.Correctness

@[expose] public section
namespace RotationBST.TreeBuffer.Scan

/-- Correct initialized node fields supply the local routing view directly.
The only field lookup is at the current cursor key. -/
theorem stored_route (s : State) (valid : s.Valid) (pending : s.requests ≠ [])
    (cursor : Pointer.Config) (tree : cursor.tree = s.tree) (key : cursor.key? = some s.position)
    (fields : Nat → IntervalMetadata.Bounds)
    (initialized : Metadata.label fields s.tree 0 = IntervalMetadata.label s.tree 0)
    (different : s.position ≠ s.target) :
    ∃ next position,
      Pointer.Routing.next ⟨(fields s.position).low, s.position, (fields s.position).high⟩ cursor s.target = some next ∧
      Step s { s with tree := next.tree, position := position } 1 0 := by
  have view := IntervalMetadata.Initialization.read_view fields cursor s.position key (by simpa only [tree] using initialized)
  exact local_route s valid pending cursor tree key _ view different

end RotationBST.TreeBuffer.Scan
