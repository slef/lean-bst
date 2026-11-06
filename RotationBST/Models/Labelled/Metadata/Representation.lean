module

public import RotationBST.Models.Labelled.Metadata.Definitions.Abstract
public import RotationBST.Models.Rotation.Rotations
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Metadata

theorem label_erase {α : Type} (data : Nat → α) (t : Tree) (lo : Nat) : (label data t lo).erase = t := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir => simp only [label, LabelledTree.erase, il, ir]

/-- Payloads outside the represented interval have no effect on stored nodes. -/
theorem label_congr {α : Type} (data other : Nat → α) (t : Tree) (lo : Nat)
    (same : ∀ x, lo ≤ x → x < lo + t.size → data x = other x) : label data t lo = label other t lo := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    have root := same (lo + l.size) (by omega) (by simp only [Tree.size]; omega)
    have left := il lo (fun x low high => same x low (by simp only [Tree.size]; omega))
    have right := ir (lo + l.size + 1) (fun x low high => same x (by omega) (by simp only [Tree.size]; omega))
    simp only [label, root, left, right]

/-- Rotations carry the key and its payload together, with no cell relocation
or metadata copying operation hidden in the shape change. -/
theorem label_rotate {α : Type} (data : Nat → α) {s t : Tree} (rotation : Rotate s t) (lo : Nat) :
    LabelledTree.Rotate (label data s lo) (label data t lo) := by
  induction rotation generalizing lo with
  | right => simp only [label, Tree.size, Nat.add_assoc]; exact .right
  | left => simp only [label, Tree.size, Nat.add_assoc]; exact .left
  | inLeft rotation ih => simp only [label, rotation.size_eq]; exact .inLeft (ih lo)
  | inRight _ ih => exact .inRight (ih _)

theorem label_at {α : Type} (data : Nat → α) (t : Tree) (lo x : Nat)
    (low : lo ≤ x) (high : x < lo + t.size) : At (label data t lo) x (data x) := by
  induction t generalizing lo with
  | nil => simp only [Tree.size] at high; omega
  | node l r il ir =>
    by_cases left : x < lo + l.size
    · exact .left (il lo low left)
    · by_cases root : x = lo + l.size
      · subst x; exact .root _ _ _ _
      · apply At.right
        exact ir (lo + l.size + 1) (by omega) (by simp only [Tree.size] at high; omega)

/-- A field observed at a labelled node is exactly its key-associated value. -/
theorem at_payload {α : Type} (data : Nat → α) (t : Tree) (lo x : Nat) (value : α)
    (atNode : At (label data t lo) x value) : value = data x := by
  induction t generalizing lo with
  | nil => cases atNode
  | node l r il ir =>
    cases atNode with
    | root => rfl
    | left atNode => exact il lo atNode
    | right atNode => exact ir (lo + l.size + 1) atNode

private theorem update_outside {α : Type} (data : Nat → α) (value : α) (t : Tree) (lo x : Nat)
    (outside : x < lo ∨ lo + t.size ≤ x) : label (Function.update data x value) t lo = label data t lo := by
  apply label_congr
  intro y low high
  exact Function.update_of_ne (by omega) _ _

/-- A cursor-key update is exactly one labelled-node payload replacement. -/
theorem label_write {α : Type} (data : Nat → α) (value : α) (t : Tree) (lo x : Nat)
    (low : lo ≤ x) (high : x < lo + t.size) :
    Write (label data t lo) x value (label (Function.update data x value) t lo) := by
  induction t generalizing lo with
  | nil => simp only [Tree.size] at high; omega
  | node l r il ir =>
    by_cases left : x < lo + l.size
    · have other := update_outside data value r (lo + l.size + 1) x (Or.inl (by omega))
      have root : lo + l.size ≠ x := by omega
      simp only [label, Function.update_of_ne root, other]
      exact .left (il lo low left)
    · by_cases root : x = lo + l.size
      · subst x
        have left := update_outside data value l lo (lo + l.size) (Or.inr le_rfl)
        have right := update_outside data value r (lo + l.size + 1) (lo + l.size) (Or.inl (by omega))
        simp only [label, Function.update_self, left, right]
        exact .root _ _ _ _ _
      · have other := update_outside data value l lo x (Or.inr (by omega))
        have root : lo + l.size ≠ x := by omega
        simp only [label, Function.update_of_ne root, other]
        exact .right (ir (lo + l.size + 1) (by omega) (by simp only [Tree.size] at high; omega))

end RotationBST.Metadata
