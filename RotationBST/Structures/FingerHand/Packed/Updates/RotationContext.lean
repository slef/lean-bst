module

public import RotationBST.Structures.FingerHand.Packed.Updates.RotationMarks
public import RotationBST.Structures.FingerHand.Packed.Neighbors.Location

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem Context.rotation_labels (fs : List ContextFrame) {a b : Hand}
    (size : a.reference.size = b.reference.size)
    (rotation : ∀ lo, LabelledTree.Rotate (a.labels lo) (b.labels lo)) (lo : Nat) :
    LabelledTree.Rotate ((Context.plug fs a).labels lo) ((Context.plug fs b).labels lo) := by
  induction fs generalizing a b with
  | nil => exact rotation lo
  | cons f fs ih =>
    cases f with
    | left cs d r =>
      apply ih
      · apply Pointer.plug_size_congr
        simp only [Tree.size, size]
      · intro base
        simp only [labels, size]
        exact .inLeft (rotation _)
    | right cs d l =>
      apply ih
      · apply Pointer.plug_size_congr
        simp only [Tree.size, size]
      · intro base
        exact .inRight (rotation _)

/-- Canonical marked rotation lifts through arbitrary enclosing hand regions.
Their incoming paths may be contracted and their roots need not be marked. -/
theorem LocalRotation.canonical_under {a b : Hand} (rot : LocalRotation a b)
    (fs : List ContextFrame) (marks : Finset Nat) (lo : Nat)
    (marked : MarkedRotation marks
      (a.reference.labelFrom (lo + Pointer.offset (Context.referencePath fs)))
      (b.reference.labelFrom (lo + Pointer.offset (Context.referencePath fs))))
    (canonical : (Context.plug fs a).labels lo = compress marks (Context.plug fs a).reference lo) :
    (Context.plug fs b).labels lo = compress marks (Context.plug fs b).reference lo := by
  apply rotation_canonical marks lo (Context.rotation_labels fs rot.reference.size_eq rot.labels lo)
    _ canonical
  simpa only [Context.plug_reference] using marked.under_path (Context.referencePath fs) lo

/-- The physical rotation and its exact size/potential accounting lift through
the same enclosing hand, with both navigation directions charged. -/
theorem LocalRotation.trace_under {a b : Hand} (rot : LocalRotation a b)
    (fs : List ContextFrame) (valid : (Context.plug fs a).Valid) :
    (Context.plug fs b).Valid ∧ (Context.plug fs b).count = (Context.plug fs a).count ∧
      (Context.plug fs b).potential = (Context.plug fs a).potential ∧
      ∃ k, Pointer.Trace ⟨(Context.plug fs a).tree, []⟩ ⟨(Context.plug fs b).tree, []⟩ k ∧
        k + (Context.plug fs b).potential ≤ 10 + 10 * fs.length + (Context.plug fs a).potential := by
  obtain ⟨inside, outside⟩ := (Context.plug_valid_iff fs a).mp valid
  refine ⟨Context.plug_valid outside (rot.valid inside), ?_, ?_, ?_⟩
  · simp only [Context.plug_count, rot.count]
  · simp only [Context.plug_potential, rot.potential]
  · obtain ⟨k, bound, trace⟩ := rot.trace
    have nonempty : a.tree ≠ .nil ∧ b.tree ≠ .nil := by
      cases rot <;> constructor <;> exact Pointer.plug_ne_nil _ (by simp)
    exact Context.lift_trace fs trace nonempty.1 nonempty.2 (by rw [rot.potential]; omega)

end RotationBST.FingerHand.Hand
