module

public import RotationBST.Structures.TreeBuffer.Scan.Requests
public import RotationBST.Bounds.LazyFinger.Edges.Rotations
public import RotationBST.Models.Pointer.Walk.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Scan

theorem potential_le (s : State) (valid : s.Valid) : potential s ≤ 4 * s.tree.size := by
  rw [potential, LazyFinger.costFrom_eq_crossings _ _ _ valid.1 (requests_valid s valid)]
  have bound := LazyFinger.intervalCost_le_size
    (fun lo hi => LazyFinger.crossings lo hi s.position s.requests) 3 (requests_crossings s) s.tree 0
  have length := requests_length_le s valid
  omega

theorem Step.valid {s t : State} {k r : Nat} (step : Step s t k r) (valid : s.Valid) : t.Valid := by
  cases step with
  | move tree move _ key _ _ =>
    exact ⟨Pointer.Config.key_lt_size _ _ key, by simpa only [← tree, move.tree_eq] using valid.2⟩
  | visit pending _ => exact afterVisit_valid _ valid pending
  | rotate rotation => simpa only [State.Valid, ← rotation.size_eq] using valid

/-- A primitive scan move or visit decreases potential by one. A rotation
increases it by at most three, for either traversal direction. -/
theorem Step.potential_bound {s t : State} {k r : Nat} (step : Step s t k r) (valid : s.Valid) :
    k + potential t ≤ potential s + 3 * r := by
  cases step with
  | @move a b y tree move keyA keyB pending closer =>
    have same : b.tree = s.tree := move.tree_eq.symm.trans tree
    have requests : ({ s with tree := b.tree, position := y } : State).requests = s.requests := by
      simp only [State.requests, same]
    change 1 + LazyFinger.costFrom b.tree y ({ s with tree := b.tree, position := y } : State).requests ≤
      LazyFinger.costFrom s.tree s.position s.requests + 3 * 0
    rw [requests, same, requests_cons s pending]
    simp only [LazyFinger.costFrom]
    rw [same] at closer
    omega
  | visit pending arrived =>
    have validTarget := target_valid s valid pending
    have self := LazyFinger.distance_self s.tree s.target validTarget
    have split := requests_cons s pending
    change 1 + LazyFinger.costFrom s.tree s.position s.afterVisit.requests ≤
      LazyFinger.costFrom s.tree s.position s.requests + 3 * 0
    rw [split, LazyFinger.costFrom, arrived, self]
    omega
  | @rotate t rotation =>
    have same := rotation.size_eq
    have requests : ({ s with tree := t } : State).requests = s.requests := by
      simp only [State.requests, ← same]
    have bound := LazyFinger.costFrom_rotate_le rotation s.position s.requests valid.1
      (requests_valid s valid) 3 (requests_crossings s)
    simpa only [potential, requests, Nat.zero_add, Nat.mul_one] using bound

theorem Trace.amortized {s t : State} {work rotations : Nat} (trace : Trace s t work rotations)
    (valid : s.Valid) : work + potential t ≤ potential s + 3 * rotations := by
  induction trace with
  | refl => simp
  | step step _ ih =>
    have first := step.potential_bound valid
    have rest := ih (step.valid valid)
    omega

/-- Every prefix costs `O(n+r)`, even with rotations during movement toward
the next cell, in forward or reverse inorder. -/
theorem Trace.cost {s t : State} {work rotations : Nat} (trace : Trace s t work rotations)
    (valid : s.Valid) : work ≤ 4 * s.tree.size + 3 * rotations := by
  have amortized := trace.amortized valid
  have initial := potential_le s valid
  omega

theorem Trace.total_cost {s t : State} {work rotations : Nat} (trace : Trace s t work rotations)
    (valid : s.Valid) : work + rotations ≤ 4 * s.tree.size + 4 * rotations := by
  have bound := trace.cost valid
  omega

end RotationBST.TreeBuffer.Scan
