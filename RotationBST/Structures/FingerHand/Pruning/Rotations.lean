module

public import RotationBST.Structures.FingerHand.Pruning.Basic
public import RotationBST.Models.Pointer.Navigation

@[expose] public section
namespace RotationBST.FingerHand

theorem MarkedRotation.rotate {marks : Finset Nat} {s t : LabelledTree Nat}
    (h : MarkedRotation marks s t) : LabelledTree.Rotate s t := by
  induction h with
  | right => exact .right
  | left => exact .left
  | inLeft _ ih => exact .inLeft ih
  | inRight _ ih => exact .inRight ih

theorem MarkedRotation.symm {marks : Finset Nat} {s t : LabelledTree Nat}
    (h : MarkedRotation marks s t) : MarkedRotation marks t s := by
  induction h with
  | right hx hy => exact .left hx hy
  | left hx hy => exact .right hx hy
  | inLeft _ ih => exact .inLeft ih
  | inRight _ ih => exact .inRight ih

private theorem rotate_nonempty {s t : LabelledTree Nat} (h : LabelledTree.Rotate s t) :
    s ≠ .nil ∧ t ≠ .nil := by cases h <;> simp

private theorem join_rotate_left (marks : Finset Nat) {a b : LabelledTree Nat}
    (h : LabelledTree.Rotate a b) (x : Nat) (r : LabelledTree Nat) :
    LabelledTree.Rotate (join marks a x r) (join marks b x r) := by
  have ne := rotate_nonempty h
  cases a <;> cases b <;> simp only [ne_eq, not_true_eq_false, false_and, and_false] at ne
  by_cases hx : x ∈ marks
  · simpa only [join, hx, ↓reduceIte] using LabelledTree.Rotate.inLeft (c := r) (x := x) h
  · cases r
    · simpa only [join, hx, ↓reduceIte] using h
    · simpa only [join, hx, ↓reduceIte] using LabelledTree.Rotate.inLeft h

private theorem join_rotate_right (marks : Finset Nat) {a b : LabelledTree Nat}
    (h : LabelledTree.Rotate a b) (x : Nat) (l : LabelledTree Nat) :
    LabelledTree.Rotate (join marks l x a) (join marks l x b) := by
  have ne := rotate_nonempty h
  cases a <;> cases b <;> simp only [ne_eq, not_true_eq_false, false_and, and_false] at ne
  by_cases hx : x ∈ marks
  · simpa only [join, hx, ↓reduceIte] using LabelledTree.Rotate.inRight (c := l) (x := x) h
  · cases l
    · simpa only [join, hx, ↓reduceIte] using h
    · simpa only [join, hx, ↓reduceIte] using LabelledTree.Rotate.inRight h

/-- Compression commutes with an exposed rotation when both participating
keys are marked, including beneath contracted enclosing paths. -/
theorem MarkedRotation.project {marks : Finset Nat} {s t : LabelledTree Nat}
    (h : MarkedRotation marks s t) : LabelledTree.Rotate (prune marks s) (prune marks t) := by
  induction h with
  | right hx hy => simp only [prune, join, hx, hy, ↓reduceIte]; exact .right
  | left hx hy => simp only [prune, join, hx, hy, ↓reduceIte]; exact .left
  | inLeft _ ih => exact join_rotate_left marks ih _ _
  | inRight _ ih => exact join_rotate_right marks ih _ _

theorem MarkedRotation.under_path (cs : List Pointer.Frame) {s t : Tree} (lo : Nat)
    {marks : Finset Nat} (h : MarkedRotation marks
      (s.labelFrom (lo + Pointer.offset cs)) (t.labelFrom (lo + Pointer.offset cs))) :
    MarkedRotation marks ((Pointer.plug cs s).labelFrom lo) ((Pointer.plug cs t).labelFrom lo) := by
  induction cs generalizing s t lo with
  | nil => simpa only [Pointer.plug, Pointer.offset, Nat.add_zero] using h
  | cons f cs ih =>
    have size : s.size = t.size := by
      have eq := (Representation.Bridge.erase_rotate h.rotate).size_eq
      simpa only [Representation.Bridge.erase_label] using eq
    cases f with
    | left g =>
      apply ih
      simp only [Tree.labelFrom, size]
      apply MarkedRotation.inLeft
      simpa only [Pointer.offset] using h
    | right g =>
      apply ih
      apply MarkedRotation.inRight
      simpa only [Pointer.offset, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end RotationBST.FingerHand
