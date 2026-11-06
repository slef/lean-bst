module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Step
public import RotationBST.Models.Multifinger.Program.Replay.Abstract

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation
open LabelledCursor

theorem response_exists_within {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    {op : Multifinger.Opcode} (valid : ConfigValid weight c s)
    (legal : (perform op c).isSome = true) :
    ∃ out : Output α, perform op c = some out.source ∧ ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 + s.potential ∧
      (out.cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
        Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
        ∀ x, Tree.depth middle.tree x ≤ 16 * Tree.depth s.pair.tree x + 96 := by
  cases eq : perform op c with
  | none => simp [eq] at legal
  | some next =>
    obtain ⟨after, cost, preserved, trace, bound, worst⟩ := step_within valid eq
    obtain ⟨instructions, length, replay, prefixes⟩ := trace.record
    refine ⟨⟨next, after, instructions⟩, rfl, preserved, replay, ?_, ?_, ?_⟩
    · simpa only [Output.cost, length] using bound
    · simpa only [Output.cost, length] using worst

    · intro cut
      obtain ⟨middle, first, last, bounds⟩ := prefixes cut
      exact ⟨middle, first, last, bounds.2⟩

theorem response_exists_bounded {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    {op : Multifinger.Opcode} (valid : ConfigValid weight c s)
    (legal : (perform op c).isSome = true) :
    ∃ out : Output α, perform op c = some out.source ∧ ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 + s.potential ∧
      (out.cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨out, source, valid, replay, bound, worst, _⟩ := response_exists_within valid legal
  exact ⟨out, source, valid, replay, bound, worst⟩

/-- Fix one choice at each current configuration, independently of the future.
As elsewhere in the abstract online model, internal planning is not charged. -/
noncomputable def policy {α : Type} (weight : α → ℝ) : Policy α := by
  classical
  exact fun c s op =>
    if valid : ConfigValid weight c s then
      if legal : (perform op c).isSome = true then
        some (Classical.choose (response_exists_within valid legal))
      else none
    else none

theorem policy_valid {α : Type} (weight : α → ℝ) : PolicyValid weight (policy weight) := by
  classical
  intro c s op valid
  cases eq : perform op c with
  | none => simp [policy, valid, eq]
  | some next =>
    have legal : (perform op c).isSome = true := by simp [eq]
    have spec := Classical.choose_spec (response_exists_within valid legal)
    refine ⟨Classical.choose (response_exists_within valid legal), ?_, ?_, spec.2.1, spec.2.2.1, spec.2.2.2.1⟩
    · simp [policy, valid, legal]
    · exact Option.some.inj (spec.1.symm.trans eq)

theorem policy_exists {α : Type} (weight : α → ℝ) : ∃ p : Policy α, PolicyValid weight p :=
  ⟨policy weight, policy_valid weight⟩

theorem response_exists {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    {op : Multifinger.Opcode} (valid : ConfigValid weight c s)
    (legal : (perform op c).isSome = true) :
    ∃ out : Output α, perform op c = some out.source ∧ ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 + s.potential := by
  obtain ⟨out, source, preserved, replay, amortized, _, _⟩ := response_exists_within valid legal
  exact ⟨out, source, preserved, replay, amortized⟩

theorem policy_bounded {α : Type} (weight : α → ℝ) : PolicyBounded weight (policy weight) := by
  classical
  refine ⟨policy_valid weight, ?_⟩
  intro c s op out valid response
  by_cases legal : (perform op c).isSome = true
  · have chosen := Classical.choose_spec (response_exists_within valid legal)
    have eq : Classical.choose (response_exists_within valid legal) = out := by
      simpa only [policy, dite_eq_left valid, dite_eq_left legal, Option.some.injEq] using response
    rw [← eq]
    exact chosen.2.2.2.2.1
  · simp [policy, valid, legal] at response

theorem policy_bounded_exists {α : Type} (weight : α → ℝ) : ∃ p : Policy α, PolicyBounded weight p :=
  ⟨policy weight, policy_bounded weight⟩

theorem policy_within {α : Type} (weight : α → ℝ) : PolicyWithin weight (policy weight) := by
  classical
  refine ⟨policy_bounded weight, ?_⟩
  intro c s op out valid response
  by_cases legal : (perform op c).isSome = true
  · have chosen := Classical.choose_spec (response_exists_within valid legal)
    have eq : Classical.choose (response_exists_within valid legal) = out := by
      simpa only [policy, dite_eq_left valid, dite_eq_left legal, Option.some.injEq] using response
    rw [← eq]
    exact chosen.2.2.2.2.2
  · simp [policy, valid, legal] at response

theorem policy_within_exists {α : Type} (weight : α → ℝ) : ∃ p : Policy α, PolicyWithin weight p :=
  ⟨policy weight, policy_within weight⟩

end RotationBST.HeavyPath.Finger.History.Simulation
