module

public import RotationBST.Structures.FingerHand.Packed.Simulation.Movement
public import RotationBST.Structures.FingerHand.Packed.Simulation.Rotation

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Uniform simulation of all six multifinger instructions. The final hand
represents the actual target state, including rotations and coincident fingers. -/
theorem simulate_step {fingers : Nat} {h : Hand} {s t : Multifinger.State fingers}
    {i : Fin fingers} (rep : h.Represents s) (valid : s.Valid) (step : Multifinger.Step s i t) :
    ∃ (after : Hand) (k : Nat), after.Represents t ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 344 + 60 * (fingers + 1) + h.potential := by
  cases step with
  | @execute a b x tree key instruction touched =>
    have execution := Multifinger.Step.execute tree key instruction touched
    cases instruction with
    | downLeft =>
      obtain ⟨after, k, target, trace, cost⟩ := simulate_move rep valid execution tree
      exact ⟨after, k, target, trace, by omega⟩
    | downRight =>
      obtain ⟨after, k, target, trace, cost⟩ := simulate_move rep valid execution tree
      exact ⟨after, k, target, trace, by omega⟩
    | upLeft =>
      obtain ⟨after, k, target, trace, cost⟩ := simulate_move rep valid execution tree
      exact ⟨after, k, target, trace, by omega⟩
    | upRight =>
      obtain ⟨after, k, target, trace, cost⟩ := simulate_move rep valid execution tree
      exact ⟨after, k, target, trace, by omega⟩
    | @rotateLeftChild a b c anc =>
      have finger : s.position i = Pointer.offset anc + a.size := (Option.some.inj key).symm
      have same : x = s.position i := (Option.some.inj touched).symm.trans finger.symm
      rw [same, Function.update_eq_self]
      exact simulate_rotate_right i rep valid a b c anc tree.symm finger
    | @rotateRightChild b c a anc =>
      have finger : s.position i = Pointer.offset anc + a.size + 1 + b.size := (Option.some.inj key).symm
      have index := Option.some.inj touched
      simp only [Tree.size] at index
      have same : x = s.position i := by omega
      rw [same, Function.update_eq_self]
      exact simulate_rotate_left i rep valid a b c anc tree.symm finger

/-- Instruction traces have one contiguous pointer implementation. Potentials
telescope across the exact maintained hands produced by successive steps. -/
theorem simulate_trace {fingers : Nat} {h : Hand} {s t : Multifinger.State fingers}
    {touches : List Nat} (rep : h.Represents s) (valid : s.Valid)
    (run : Multifinger.Trace s touches t) :
    ∃ (after : Hand) (k : Nat), after.Represents t ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ (344 + 60 * (fingers + 1)) * touches.length + h.potential := by
  induction run generalizing h with
  | refl => exact ⟨h, 0, rep, .refl, by simp⟩
  | step step tail ih =>
    obtain ⟨middle, k, middleRep, first, firstCost⟩ := simulate_step rep valid step
    obtain ⟨after, m, target, rest, restCost⟩ := ih middleRep (step.valid valid)
    refine ⟨after, k + m, target, first.append rest, ?_⟩
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at restCost ⊢
    omega

end RotationBST.FingerHand.Hand
