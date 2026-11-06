module

public import RotationBST.Structures.TreeBuffer.Scan.Definitions.Abstract
public import RotationBST.Bounds.LazyFinger.Sequential.Scanning
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Scan

theorem requests_valid (s : State) (valid : s.Valid) : ∀ x ∈ s.requests, x < s.tree.size := by
  intro x member
  unfold State.requests at member
  split at member
  · have bound := List.mem_range.mp (List.mem_reverse.mp member)
    have limit := valid.2
    omega
  · have bounds := List.mem_range'.mp member
    omega

theorem requests_crossings (s : State) (lo hi : Nat) :
    LazyFinger.crossings lo hi s.position s.requests ≤ 3 := by
  unfold State.requests
  split
  · exact LazyFinger.crossings_reverse_range lo hi s.position s.next
  · exact LazyFinger.crossings_range' lo hi s.position s.next (s.tree.size - s.next)

theorem requests_length_le (s : State) (valid : s.Valid) : s.requests.length ≤ s.tree.size := by
  unfold State.requests
  split
  · simpa only [List.length_reverse, List.length_range] using valid.2
  · simp only [List.length_range']; omega

/-- Visiting the target removes exactly the head of the pending scan in either
direction, so no cells can be skipped or repeated. -/
theorem requests_cons (s : State) (pending : s.requests ≠ []) :
    s.requests = s.target :: s.afterVisit.requests := by
  cases direction : s.descending with
  | false =>
    have positive : 0 < s.tree.size - s.next := by
      have nonzero : s.tree.size - s.next ≠ 0 := by
        intro zero
        simp [State.requests, direction, zero] at pending
      omega
    have length : s.tree.size - s.next = (s.tree.size - (s.next + 1)) + 1 := by omega
    simp only [State.requests, State.target, State.afterVisit, direction, Bool.false_eq_true, ↓reduceIte, length, List.range']
  | true =>
    have positive : 0 < s.next := by
      have nonzero : s.next ≠ 0 := by intro zero; simp [State.requests, direction, zero] at pending
      omega
    have length : s.next = (s.next - 1) + 1 := by omega
    simp only [State.requests, State.target, State.afterVisit, direction, ↓reduceIte]
    conv_lhs => rw [length, List.range_succ]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]

theorem target_valid (s : State) (valid : s.Valid) (pending : s.requests ≠ []) : s.target < s.tree.size :=
  requests_valid s valid s.target (by rw [requests_cons s pending]; exact List.mem_cons_self)

theorem afterVisit_valid (s : State) (valid : s.Valid) (pending : s.requests ≠ []) : s.afterVisit.Valid := by
  have target := target_valid s valid pending
  unfold State.afterVisit State.Valid State.target at *
  split <;> simp_all; omega

end RotationBST.TreeBuffer.Scan
