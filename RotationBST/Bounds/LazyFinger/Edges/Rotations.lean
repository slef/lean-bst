module

public import RotationBST.Bounds.LazyFinger.Edges.Sequence
public import RotationBST.Models.Rotation.Rotations
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

/-- A rotation replaces only one proper-subtree interval. If each boundary toll
is at most `C`, the total interval objective increases by at most `C`. -/
theorem intervalCost_rotate_le (w : Nat → Nat → Nat) (C : Nat)
    (bounded : ∀ lo hi, w lo hi ≤ C) {s t : Tree} (rotation : Rotate s t) (lo : Nat) :
    intervalCost w t lo ≤ intervalCost w s lo + C := by
  induction rotation generalizing lo with
  | @right a b c =>
    have new := bounded (lo + a.size + 1) (lo + a.size + 1 + (b.size + 1 + c.size))
    simp only [intervalCost, Tree.size]
    simp only [Nat.add_assoc] at new ⊢
    omega
  | @left a b c =>
    have new := bounded lo (lo + (a.size + 1 + b.size))
    simp only [intervalCost, Tree.size]
    simp only [Nat.add_assoc] at new ⊢
    omega
  | @inLeft a b r rotation ih =>
    have same := rotation.size_eq
    have bound := ih lo
    simp only [intervalCost, Tree.size, ← same]
    omega
  | @inRight a b l rotation ih =>
    have same := rotation.size_eq
    have bound := ih (lo + l.size + 1)
    simp only [intervalCost, Tree.size, ← same]
    omega

/-- Sequence movement is stable under rotations whenever its crossing count
per subtree interval is bounded. The requests themselves do not change. -/
theorem costFrom_rotate_le {s t : Tree} (rotation : Rotate s t) (p : Nat) (xs : List Nat)
    (initial : p < s.size) (valid : ∀ x ∈ xs, x < s.size) (C : Nat)
    (bounded : ∀ lo hi, crossings lo hi p xs ≤ C) :
    costFrom t p xs ≤ costFrom s p xs + C := by
  have size := rotation.size_eq
  rw [costFrom_eq_crossings s p xs initial valid,
    costFrom_eq_crossings t p xs (by omega) (by intro x hx; rw [← size]; exact valid x hx)]
  have bound := intervalCost_rotate_le (fun lo hi => crossings lo hi p xs) C bounded rotation 0
  omega

end RotationBST.LazyFinger
