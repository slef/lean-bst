module

public import RotationBST.Algorithms.Combination.Rounds.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Rounds

theorem partition_length (side : Bool) (start stop : Nat) (boundaries : List Nat) :
    (partition side start stop boundaries).length = boundaries.length + 1 := by
  induction boundaries generalizing side start with
  | nil => rfl
  | cons boundary rest ih => simp only [partition, List.length_cons, ih]

/-- All spans lie within the prefix, including the interrupted request at the
closing boundary of each round. -/
theorem partition_bounds (side : Bool) (start stop : Nat) (boundaries : List Nat)
    (range : start ≤ stop) (ordered : boundaries.Pairwise (· < ·))
    (inside : ∀ i ∈ boundaries, start ≤ i ∧ i < stop) :
    ∀ span ∈ partition side start stop boundaries,
      start ≤ span.start ∧ span.start ≤ span.stop ∧ span.stop ≤ stop := by
  induction boundaries generalizing side start with
  | nil => intro span member; simp only [partition, List.mem_singleton] at member; subst span; exact ⟨le_rfl, range, le_rfl⟩
  | cons boundary rest ih =>
    have bound := inside boundary (List.mem_cons_self ..)
    have ordering := List.pairwise_cons.mp ordered
    intro span member
    rcases List.mem_cons.mp member with rfl | member
    · dsimp
      exact ⟨le_rfl, by omega, by omega⟩
    · have tailInside : ∀ i ∈ rest, boundary ≤ i ∧ i < stop := by
        intro i member
        exact ⟨(ordering.1 i member).le, (inside i (List.mem_cons_of_mem _ member)).2⟩
      have result := ih (!side) boundary bound.2.le ordering.2 tailInside span member
      exact ⟨by omega, result.2⟩

/-- A span belonging to the opposite worker begins no earlier than the first
switch. This is the one-boundary gap used to separate same-worker rounds. -/
theorem opposite_start (side : Bool) (start stop boundary : Nat) (rest : List Nat)
    (_range : start ≤ boundary) (last : boundary < stop)
    (ordered : (boundary :: rest).Pairwise (· < ·)) (inside : ∀ i ∈ rest, i < stop)
    (span : Span) (member : span ∈ partition side start stop (boundary :: rest)) (different : span.side ≠ side) :
    boundary ≤ span.start := by
  rcases List.mem_cons.mp member with rfl | member
  · exact False.elim (different rfl)
  · have ordering := List.pairwise_cons.mp ordered
    exact (partition_bounds (!side) boundary stop rest last.le ordering.2
      (fun i member => ⟨(ordering.1 i member).le, inside i member⟩) span member).1

/-- Strict switch positions and alternating workers prevent any request
position from being assigned to two different rounds of the same worker. -/
theorem partition_separated (side : Bool) (start stop : Nat) (boundaries : List Nat)
    (range : start ≤ stop) (ordered : boundaries.Pairwise (· < ·))
    (inside : ∀ i ∈ boundaries, start ≤ i ∧ i < stop) :
    Separated (partition side start stop boundaries) := by
  induction boundaries generalizing side start with
  | nil => simp [partition, Separated]
  | cons boundary rest ih =>
    have bound := inside boundary (List.mem_cons_self ..)
    have ordering := List.pairwise_cons.mp ordered
    have tailInside : ∀ i ∈ rest, boundary ≤ i ∧ i < stop := by
      intro i member
      exact ⟨(ordering.1 i member).le, (inside i (List.mem_cons_of_mem _ member)).2⟩
    refine List.pairwise_cons.mpr ⟨?_, ih (!side) boundary bound.2.le ordering.2 tailInside⟩
    intro span member same
    change side = span.side at same
    change boundary + 1 ≤ span.start
    cases rest with
    | nil =>
      simp only [partition, List.mem_singleton] at member
      subst span
      cases side <;> contradiction
    | cons next rest =>
      have nextBound := tailInside next (List.mem_cons_self ..)
      have later := opposite_start (!side) boundary stop next rest nextBound.1 nextBound.2 ordering.2
        (fun i member => (tailInside i (List.mem_cons_of_mem _ member)).2) span member
        (by rw [← same]; cases side <;> decide)
      have strict := ordering.1 next (List.mem_cons_self ..)
      omega

/-- For either selected worker, alternating round counts differ by at most
one. The empty input still has its initial, possibly empty, round. -/
theorem partition_count (selected side : Bool) (start stop : Nat) (boundaries : List Nat) :
    (partition side start stop boundaries).length ≤ 2 * count selected (partition side start stop boundaries) + 1 := by
  induction boundaries using List.twoStepInduction generalizing side start with
  | nil => cases selected <;> cases side <;> simp [partition, count]
  | singleton boundary => cases selected <;> cases side <;> simp [partition, count]
  | cons_cons first second rest ih =>
    have tail := ih side second
    cases selected <;> cases side <;> simp [partition, count] at tail ⊢ <;> omega

end RotationBST.Combo.Rounds
