module

public import RotationBST.Structures.TreeBuffer.Scan.Initialized
public import RotationBST.Models.Labelled.Intervals.Access.Correctness

@[expose] public section
namespace RotationBST.TreeBuffer.Scan

/-- A four-unit read-and-move on the explicitly labelled cursor realizes one
navigation step of the scan accounting, and preserves its routing annotation. -/
theorem labelled_route (s : State) (valid : s.Valid) (pending : s.requests ≠ [])
    (cursor : LabelledCursor.Config (Nat × IntervalMetadata.Bounds))
    (canonical : IntervalMetadata.Access.Canonical cursor)
    (tree : cursor.erase.tree = s.tree) (bounds : IntervalMetadata.Bounds)
    (read : cursor.read = some (s.position, bounds)) (different : s.position ≠ s.target) :
    ∃ next position, IntervalMetadata.Access.route s.target cursor = some (4, next) ∧
      Step s { s with tree := next.erase.tree, position := position } 1 0 ∧
      IntervalMetadata.Access.Canonical next := by
  have fields := IntervalMetadata.Access.read_valid cursor canonical s.position bounds read
  obtain ⟨next, position, execution, physical, atKey, closer, nextCanonical⟩ :=
    IntervalMetadata.Access.progress s.target cursor canonical s.position bounds read
      (by rw [tree]; exact target_valid s valid pending) different
  exact ⟨next, position, execution,
    .move tree physical fields.2.1 atKey pending (by simpa only [tree] using closer), nextCanonical⟩

end RotationBST.TreeBuffer.Scan
