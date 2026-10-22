import Std

/-! A bounded least-consistent-hypothesis learner stabilizes. This handles the
learning ingredient of a periodic probe, not its BST serving-cost guarantee. -/
namespace RotationBST

theorem bounded_monotone_stabilizes (h : Nat → Nat) (N : Nat)
    (bound : ∀ i, h i ≤ N) (mono : ∀ i j, i ≤ j → h i ≤ h j) :
    ∃ cutoff, ∀ i, cutoff ≤ i → h i = h cutoff := by
  induction N with
  | zero => exact ⟨0, fun i _ => by have := bound i; have := bound 0; omega⟩
  | succ N ih =>
      by_cases hit : ∃ i, h i = N + 1
      · obtain ⟨i, hi⟩ := hit
        exact ⟨i, fun j hj => by have := mono i j hj; have := bound j; omega⟩
      · apply ih
        intro i
        have hb := bound i
        have hn : h i ≠ N + 1 := fun he => hit ⟨i, he⟩
        omega

/-- Compatibility shrinks with more observations. A permanently correct
hypothesis bounds the least consistent index, so the chosen index stabilizes. -/
theorem least_consistent_stabilizes (compatible : Nat → Nat → Prop)
    (chosen : Nat → Nat) (correct : Nat)
    (shrinks : ∀ i j q, i ≤ j → compatible j q → compatible i q)
    (truth : ∀ i, compatible i correct)
    (consistent : ∀ i, compatible i (chosen i))
    (least : ∀ i q, compatible i q → chosen i ≤ q) :
    ∃ cutoff, ∀ i, cutoff ≤ i → chosen i = chosen cutoff := by
  apply bounded_monotone_stabilizes chosen correct
  · intro i; exact least i correct (truth i)
  · intro i j hij
    exact least i (chosen j) (shrinks i j (chosen j) hij (consistent j))

/-- A stabilized, consistently chosen hypothesis is compatible with every
finite observed prefix, including those before stabilization. -/
theorem stabilized_hypothesis_correct (compatible : Nat → Nat → Prop)
    (chosen : Nat → Nat) (cutoff : Nat)
    (shrinks : ∀ i j q, i ≤ j → compatible j q → compatible i q)
    (consistent : ∀ i, compatible i (chosen i))
    (stable : ∀ i, cutoff ≤ i → chosen i = chosen cutoff) :
    ∀ i, compatible i (chosen cutoff) := by
  intro i
  have hc := consistent (max cutoff i)
  rw [stable _ (Nat.le_max_left _ _)] at hc
  exact shrinks i (max cutoff i) (chosen cutoff) (Nat.le_max_right _ _) hc

/-- info: 'RotationBST.least_consistent_stabilizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms least_consistent_stabilizes
end RotationBST
