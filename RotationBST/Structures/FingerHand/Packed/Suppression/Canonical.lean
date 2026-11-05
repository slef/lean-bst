module

public import RotationBST.Structures.FingerHand.Pruning.Suppression.Exact
public import RotationBST.Structures.FingerHand.Packed.Pruning
public import RotationBST.Structures.FingerHand.Packed.Neighbors.Location

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- A labelled suppression restores the exact target skeleton when its source
is canonical for the target marks plus the obsolete key. -/
theorem suppression_canonical {a b : Hand} (marks : Finset Nat) (lo x : Nat)
    (reference : b.reference = a.reference)
    (suppression : Suppress marks x (a.labels lo) (b.labels lo)) (unmarked : x ∉ marks)
    (canonical : a.labels lo = compress (insert x marks) a.reference lo) :
    b.labels lo = compress marks b.reference lo := by
  have normal : Reduced (insert x marks) (a.labels lo) := by
    rw [canonical]
    exact compress_reduced _ _ _
  have exactPruning := suppression.prune_eq unmarked (labels_distinct a lo) normal
  rw [canonical, prune_compress (Finset.subset_insert x marks)] at exactPruning
  rw [reference]
  exact exactPruning.symm

/-- A local suppression lifts through the enclosing hand, with exact global
ranks. Its nonempty retained region keeps every enclosing branch intact. -/
theorem Context.suppress (fs : List ContextFrame) {a b : Hand} {marks : Finset Nat} {x : Nat}
    (reference : a.reference = b.reference) (lo : Nat)
    (suppression : Suppress marks x (a.labels (lo + Pointer.offset (Context.referencePath fs)))
      (b.labels (lo + Pointer.offset (Context.referencePath fs)))) :
    Suppress marks x ((Context.plug fs a).labels lo) ((Context.plug fs b).labels lo) := by
  induction fs generalizing a b with
  | nil => simpa only [Context.plug, Context.referencePath, Pointer.offset, Nat.add_zero] using suppression
  | cons f fs ih =>
    cases f with
    | left cs d r =>
      apply ih (by simp only [Hand.reference, reference])
      have sub : Suppress marks x
          (a.labels (lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs))
          (b.labels (lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs)) := by
        simpa only [Context.referencePath, Pointer.offset_append, Pointer.offset,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using suppression
      simp only [labels, reference]
      exact .inLeft sub
    | right cs d l =>
      apply ih (by simp only [Hand.reference, reference])
      have sub : Suppress marks x
          (a.labels (lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size + 1))
          (b.labels (lo + Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size + 1)) := by
        simpa only [Context.referencePath, Pointer.offset_append, Pointer.offset,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using suppression
      exact .inRight sub

end RotationBST.FingerHand.Hand
