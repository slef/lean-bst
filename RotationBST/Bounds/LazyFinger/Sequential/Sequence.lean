module

public import RotationBST.Bounds.LazyFinger.Sequential.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

@[simp] theorem scans_length (n rounds : Nat) : (scans n rounds).length = rounds * n := by
  induction rounds with
  | zero => simp [scans]
  | succ rounds ih => simp only [scans, List.length_append, List.length_range, ih]; nlinarith

theorem scans_valid (n rounds : Nat) : ∀ x ∈ scans n rounds, x < n := by
  induction rounds with
  | zero => simp [scans]
  | succ rounds ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_range.mp hx
    · exact ih x hx

@[simp] theorem scans_count (n rounds x : Nat) :
    (scans n rounds).count x = if x < n then rounds else 0 := by
  induction rounds with
  | zero => simp [scans]
  | succ rounds ih => simp [scans, List.count_append, List.count_range, ih]; split <;> omega

end RotationBST.LazyFinger
