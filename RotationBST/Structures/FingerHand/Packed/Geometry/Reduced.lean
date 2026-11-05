module

public import RotationBST.Structures.FingerHand.Packed.Geometry.Intervals
public import RotationBST.Structures.FingerHand.Pruning.Suppression.Normal

@[expose] public section
namespace RotationBST.FingerHand

private theorem prune_left_member (marks : Finset Nat) (l r : LabelledTree Nat) (y x : Nat)
    (member : x ∈ (prune marks l).inorder) : x ∈ (prune marks (.node l y r)).inorder := by
  by_cases hy : y ∈ marks <;> cases hl : prune marks l <;> cases hr : prune marks r <;>
    simp_all [prune, join, LabelledTree.inorder] <;> tauto

private theorem prune_right_member (marks : Finset Nat) (l r : LabelledTree Nat) (y x : Nat)
    (member : x ∈ (prune marks r).inorder) : x ∈ (prune marks (.node l y r)).inorder := by
  by_cases hy : y ∈ marks <;> cases hl : prune marks l <;> cases hr : prune marks r <;>
    simp_all [prune, join, LabelledTree.inorder]

namespace Hand.Context

theorem reduced (fs : List ContextFrame) (h : Hand) (marks : Finset Nat) (lo : Nat)
    (normal : Reduced marks ((plug fs h).labels lo)) :
    Reduced marks (h.labels (lo + Pointer.offset (referencePath fs))) := by
  induction fs generalizing h with
  | nil => simpa only [plug, referencePath, Pointer.offset, Nat.add_zero] using normal
  | cons f fs ih =>
    cases f with
    | left cs d r =>
      have inside := (ih (.node cs d h r) normal).1
      simpa only [referencePath, Pointer.offset_append, Pointer.offset,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using inside
    | right cs d l =>
      have inside := (ih (.node cs d l h) normal).2.1
      simpa only [referencePath, Pointer.offset_append, Pointer.offset,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using inside

theorem prune_member (fs : List ContextFrame) (h : Hand) (marks : Finset Nat) (lo x : Nat)
    (member : x ∈ (prune marks (h.labels (lo + Pointer.offset (referencePath fs)))).inorder) :
    x ∈ (prune marks ((plug fs h).labels lo)).inorder := by
  induction fs generalizing h with
  | nil => simpa only [plug, referencePath, Pointer.offset, Nat.add_zero] using member
  | cons f fs ih =>
    cases f with
    | left cs d r =>
      apply ih
      apply prune_left_member
      simpa only [referencePath, Pointer.offset_append, Pointer.offset,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member
    | right cs d l =>
      apply ih
      apply prune_right_member
      simpa only [referencePath, Pointer.offset_append, Pointer.offset,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member

end Hand.Context
end RotationBST.FingerHand
