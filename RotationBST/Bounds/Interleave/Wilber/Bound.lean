module

public import RotationBST.Bounds.Interleave.Wilber.Potential
public import RotationBST.Models.Equivalence.Exact
public import RotationBST.Bounds.Interleave.Wilber.Defs

@[expose] public section
namespace RotationBST.Wilber
open Geometric

private theorem execution_valid {s t : Tree} {xs : List Nat} {cost : Nat}
    (execution : RegionExecution s xs t cost) : ∀ x ∈ xs, x < s.size := by
  induction execution with
  | nil => simp
  | @cons s v t x cost xs step tail ih =>
    have same := Region.same_of_fringe step.fringe 0
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · have := Region.keys_bounds step.visits
      simpa only [Nat.zero_add, step.source] using this.2
    · have := ih y hy
      have he : s.size = v.size := by simpa only [step.source, step.target] using same.1
      omega

theorem execution_bound (reference : Tree) (lo : Nat) (past : List Nat)
    {s t : Tree} {xs : List Nat} {cost : Nat} (execution : RegionExecution s xs t cost)
    (upper : lo + reference.size ≤ s.size) :
    absoluteInterleave reference lo (past ++ xs) + potential reference lo t (past ++ xs) ≤
      absoluteInterleave reference lo past + potential reference lo s past + 2 * cost := by
  induction execution generalizing past with
  | nil => simp
  | @cons s v t x cost xs step tail ih =>
    have same := Region.same_of_fringe step.fringe 0
    have single := amortized_step reference lo past same
      (by simpa only [step.source] using upper) step.visits
    simp only [step.source, step.target] at single
    have upperV : lo + reference.size ≤ v.size := by
      have he : s.size = v.size := by simpa only [step.source, step.target] using same.1
      omega
    have rest := ih (past ++ [x]) upperV
    simp only [List.append_assoc, List.singleton_append] at rest
    omega

/-- Wilber's interleave lower bound for actual rooted-region executions. -/
theorem interleave_le_regions (reference : Tree) {s t : Tree} {xs : List Nat} {cost : Nat}
    (size : reference.size = s.size) (execution : RegionExecution s xs t cost) :
    interleave reference xs ≤ 2 * cost := by
  have bound := execution_bound reference 0 [] execution (by omega)
  simp only [List.nil_append, absolute_empty, potential_empty, Nat.zero_add] at bound
  have valid : ∀ x ∈ xs, x < reference.size := by rw [size]; exact execution_valid execution
  rw [absoluteInterleave_eq reference xs valid] at bound
  omega

/-- The interleave quantity lower-bounds the optimum geometric solution. -/
theorem interleave_le_ass {n : Nat} {xs : List Nat} (reference : Tree) (size : reference.size = n)
    (E : Offline n xs) : interleave reference xs ≤ 2 * E.points.card := by
  obtain ⟨s, t, hs, execution⟩ := offline_to_regions E
  exact interleave_le_regions reference (size.trans hs.symm) execution

/-- Wilber's lower bound in the simplified rotation model, including requests. -/
theorem interleave_le_rotations (reference : Tree) {s t : Tree} {xs : List Nat} {r : Nat}
    (size : reference.size = s.size) (execution : RotationBST.Execution s xs t r) :
    interleave reference xs ≤ 4 * r + 2 * xs.length := by
  obtain ⟨E, hc⟩ := rotations_to_offline execution
  have := interleave_le_ass reference size E
  omega

/-- The conventional pointer model also satisfies the lower bound. -/
theorem interleave_le_pointers (reference : Tree) {s t : Tree} {xs : List Nat} {cost : Nat}
    (size : reference.size = s.size) (execution : Pointer.Execution s xs t cost) :
    interleave reference xs ≤ 12 * cost := by
  obtain ⟨E, hc⟩ := pointer_to_offline execution
  have := interleave_le_ass reference size E
  omega

end RotationBST.Wilber
