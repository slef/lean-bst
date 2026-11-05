module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Barrier.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Barrier.Results

/-- The next sweep cannot access the far side of a left barrier. -/
theorem left_step {P : Finset Point} {key stamp time request : Nat}
    (barrier : Left P key stamp) (later : stamp ≤ time) (side : key ≤ request) :
    ∀ x ∈ greedySweep time request P, key ≤ x := sweep_left barrier later side

theorem right_step {P : Finset Point} {key stamp time request : Nat}
    (barrier : Right P key stamp) (later : stamp ≤ time) (side : request ≤ key) :
    ∀ x ∈ greedySweep time request P, x ≤ key := sweep_right barrier later side

/-- Preserve the barrier and every old far-side point over a whole stream. -/
theorem left_stream {P : Finset Point} {key stamp time : Nat} (xs : List Nat)
    (barrier : Left P key stamp) (later : stamp ≤ time)
    (side : ∀ x ∈ xs, key ≤ x) :
    Left (fill greedySweep time P xs) key stamp ∧
      ∀ p : Point, p.1 < key → (p ∈ fill greedySweep time P xs ↔ p ∈ P) :=
  fill_left xs barrier later side

theorem right_stream {P : Finset Point} {key stamp time : Nat} (xs : List Nat)
    (barrier : Right P key stamp) (later : stamp ≤ time)
    (side : ∀ x ∈ xs, x ≤ key) :
    Right (fill greedySweep time P xs) key stamp ∧
      ∀ p : Point, key < p.1 → (p ∈ fill greedySweep time P xs ↔ p ∈ P) :=
  fill_right xs barrier later side

/-- Lemma 3.4 of arXiv:1810.01785, also allowing subsequent requests equal to
the barrier key. No future access can cross to the opposite side. -/
theorem no_left {n key stamp : Nat} {P : Finset Point} (xs : List Nat)
    (history : History n (stamp + 1) P) (accessed : (key, stamp) ∈ P)
    (side : ∀ x ∈ xs, key ≤ x) :
    ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → key ≤ p.1 :=
  no_left_access xs history accessed side

theorem no_right {n key stamp : Nat} {P : Finset Point} (xs : List Nat)
    (history : History n (stamp + 1) P) (accessed : (key, stamp) ∈ P)
    (side : ∀ x ∈ xs, x ≤ key) :
    ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → p.1 ≤ key :=
  no_right_access xs history accessed side

/-- Two accessed endpoints confine all later accesses while searches remain
between them. This includes either endpoint and singleton intervals. -/
theorem interval {n lo hi stamp : Nat} {P : Finset Point} (xs : List Nat)
    (history : History n (stamp + 1) P)
    (left : (lo, stamp) ∈ P) (right : (hi, stamp) ∈ P)
    (inside : ∀ x ∈ xs, lo ≤ x ∧ x ≤ hi) :
    ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → lo ≤ p.1 ∧ p.1 ≤ hi := by
  intro p hp recent
  exact ⟨no_left xs history left (fun x hx => (inside x hx).1) p hp recent,
    no_right xs history right (fun x hx => (inside x hx).2) p hp recent⟩

end RotationBST.Geometric.GreedyASS.Barrier.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Barrier.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Barrier.Results allowing [
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Algorithms.GreedyASS.Algorithm.Abstract,
  RotationBST.Algorithms.GreedyASS.Barrier.Definitions.Abstract]
