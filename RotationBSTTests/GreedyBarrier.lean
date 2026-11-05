module

public import RotationBST.Algorithms.GreedyASS.Barrier.Abstract

@[expose] public section
namespace RotationBST.Tests.GreedyBarrier
open Geometric Geometric.GreedyASS.Barrier

private def past : Finset Point := fill greedySweep 0 ∅ [1, 3, 2]

private theorem history : History 6 3 past := by unfold History; decide

-- The barrier is an access, not necessarily the searched key on its row.
-- Key 1 was projected when the last search was to key 2.
example : (1, 2) ∈ past ∧ (2, 2) ∈ past ∧ (3, 2) ∈ past := by decide

example (xs : List Nat) (side : ∀ x ∈ xs, 1 ≤ x) :
    ∀ p ∈ fill greedySweep 3 past xs, 2 < p.2 → 1 ≤ p.1 :=
  Results.no_left xs history (by decide) side

example (xs : List Nat) (side : ∀ x ∈ xs, x ≤ 3) :
    ∀ p ∈ fill greedySweep 3 past xs, 2 < p.2 → p.1 ≤ 3 :=
  Results.no_right xs history (by decide) side

-- Existing points to the far side survive, but no new ones can be added.
example : ∀ p : Point, p.1 < 2 →
    (p ∈ fill greedySweep 3 past [4, 3, 2, 5] ↔ p ∈ past) :=
  (Results.left_stream [4, 3, 2, 5] (of_history history (by decide)).1
    (by decide) (by decide)).2

example : ∀ p : Point, 2 < p.1 →
    (p ∈ fill greedySweep 3 past [0, 1, 2, 0] ↔ p ∈ past) :=
  (Results.right_stream [0, 1, 2, 0] (of_history history (by decide)).2
    (by decide) (by decide)).2

-- Requests equal to a barrier remain allowed; both endpoints confine access.
example : ∀ p ∈ fill greedySweep 3 past [1, 3, 2, 1], 2 < p.2 →
    1 ≤ p.1 ∧ p.1 ≤ 3 :=
  Results.interval [1, 3, 2, 1] history (by decide) (by decide) (by decide)

example : ∀ p ∈ fill greedySweep 3 past [2, 2, 2], 2 < p.2 →
    2 ≤ p.1 ∧ p.1 ≤ 2 :=
  Results.interval [2, 2, 2] history (by decide) (by decide) (by decide)

-- The time condition in the barrier invariant is essential. A newer far-side
-- point is still visible across an older point on the proposed barrier key.
example : (2, 0) ∈ ({(2, 0), (1, 1)} : Finset Point) ∧
    1 ∈ greedySweep 2 3 {(2, 0), (1, 1)} := by decide

-- Likewise, confining the subsequent searches is necessary.
example : 0 ∈ greedySweep 3 0 past := by decide

end RotationBST.Tests.GreedyBarrier
