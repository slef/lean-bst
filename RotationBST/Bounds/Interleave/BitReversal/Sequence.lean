module

public import RotationBST.Bounds.Interleave.BitReversal.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Wilber.BitReversal

theorem reference_size (h : Nat) : (reference h).size + 1 = 2 ^ (h + 1) := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [reference, Tree.size, pow_succ] at *; nlinarith

theorem requests_length (h : Nat) : (requests h).length = 2 ^ h := by
  induction h with
  | zero => rfl
  | succ h ih => simp [requests, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

theorem requests_valid (h : Nat) : ∀ x ∈ requests h, x < (reference h).size := by
  induction h with
  | zero => intro x hx; simp [requests] at hx; subst x; decide
  | succ h ih =>
    intro x hx
    obtain ⟨y, hy, member⟩ := List.mem_flatMap.mp hx
    have valid := ih y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    simp only [reference, Tree.size]
    rcases member with rfl | rfl <;> omega

private theorem doubled_distinct (n : Nat) (xs : List Nat) (distinct : xs.Nodup)
    (valid : ∀ x ∈ xs, x < n) :
    (xs.flatMap fun x => [x, x + n + 1]).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := valid x (by simp)
    have hxnot := (List.nodup_cons.mp distinct).1
    have tail := ih (List.nodup_cons.mp distinct).2 (by intro y hy; exact valid y (by simp [hy]))
    rw [List.flatMap_cons]
    apply List.nodup_append.mpr
    refine ⟨by simp; omega, tail, ?_⟩
    intro z first w last equal
    subst w
    obtain ⟨y, hy, hz⟩ := List.mem_flatMap.mp last
    have hyvalid := valid y (by simp [hy])
    have unequal : x ≠ y := by intro eq; subst y; exact hxnot hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at first hz
    rcases first with rfl | rfl <;> rcases hz with hz | hz <;> omega

theorem requests_distinct (h : Nat) : (requests h).Nodup := by
  induction h with
  | zero => simp [requests]
  | succ h ih => exact doubled_distinct _ _ ih (requests_valid h)

theorem requests_nonempty (h : Nat) : requests h ≠ [] := by
  intro empty
  have length := requests_length h
  rw [empty] at length
  have positive : 0 < 2 ^ h := by positivity
  simp only [List.length_nil] at length
  omega

end RotationBST.Wilber.BitReversal
