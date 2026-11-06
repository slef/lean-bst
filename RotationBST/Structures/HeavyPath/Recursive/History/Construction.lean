module

public import RotationBST.Structures.HeavyPath.Recursive.History.Accounting
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History
open Paired LabelledCursor PopTart PopTart.WeightedTree

private def entriesOf {α : Type} (payload : LabelledTree α → Tree) (credits : Frame α → Nat)
    (cs : List (Frame α)) : List (Entry α) :=
  cs.map (fun f => ⟨f, payload (framePayload f), credits f⟩)

private theorem lower_entries {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (credits : Frame α → Nat) (cs : List (Frame α)) :
    (lower (entriesOf payload credits cs)).map (Entry.slot weight) = (lowerSlotsWith weight payload cs).reverse := by
  induction cs with
  | nil => rfl
  | cons frame cs ih => cases frame <;>
      simp [entriesOf, lower, lowerSlotsWith, Entry.slot, frameMass, framePayload, ← ih]

private theorem upper_entries {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (credits : Frame α → Nat) (cs : List (Frame α)) :
    (upper (entriesOf payload credits cs)).map (Entry.slot weight) = upperSlotsWith weight payload cs := by
  induction cs with
  | nil => rfl
  | cons frame cs ih => cases frame <;>
      simp [entriesOf, upper, upperSlotsWith, Entry.slot, frameMass, framePayload, ← ih]

/-- Existing recursive constructors inhabit the history invariant. The
potential is assigned once per actual off-path occurrence. -/
theorem of_canonical_bounded {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree}
    (layout : Recursive.Layout weight t shape) :
    ∃ credit, Layout weight t shape credit ∧ credit ≤ 23 * t.erase.size := by
  induction layout with
  | nil => exact ⟨0, .nil, le_rfl⟩
  | @path t payload positive nonempty terminal children ih =>
    classical
    let credits : Frame α → Nat := fun f =>
      if h : f ∈ (extract weight t).context then Classical.choose (ih f h) else 0
    let es := entriesOf payload credits (extract weight t).context
    have charges : ∀ f ∈ (extract weight t).context, 0 ≤ frameMass weight f := by
      intro f member
      exact ((HeavyPath.Results.extract_positive positive).2 f member).le
    have fringe := Paired.Substitution.Results.buildWith_fringe payload (extract weight t).context
      Paired.Results.empty_valid charges
    have valid : PathValid weight es (Stacks.buildWith weight payload (extract weight t).context Stacks.empty) := by
      refine ⟨Paired.Substitution.Results.buildWith_valid payload _ Paired.Results.empty_valid charges, ?_, ?_⟩
      · rw [show es = entriesOf payload credits (extract weight t).context from rfl, lower_entries]
        exact fringe.1
      · rw [show es = entriesOf payload credits (extract weight t).context from rfl, upper_entries]
        exact fringe.2
    have context : es.map Entry.source = (extract weight t).context := by
      simp [es, entriesOf, List.map_map, Function.comp_def]
    refine ⟨_, .path positive nonempty context valid ?_, ?_⟩
    · intro e member
      obtain ⟨f, original, rfl⟩ := List.mem_map.mp member
      change Layout weight (framePayload f) (payload (framePayload f)) (credits f)
      simp only [credits, dite_eq_left original]
      exact (Classical.choose_spec (ih f original)).1
    · have bounds : ∀ f ∈ (extract weight t).context, credits f ≤ 23 * (framePayload f).erase.size := by
        intro f hf
        simp only [credits, dite_eq_left hf]
        exact (Classical.choose_spec (ih f hf)).2
      have summed := sum_credits_bound (extract weight t).context credits 23 bounds
      have outer := Paired.Substitution.Results.buildWith_amortized payload (extract weight t).context
        Paired.Results.empty_valid charges
      rw [show Stacks.empty.potential = 0 from rfl, Nat.add_zero] at outer
      have partition := context_size α (extract weight t).context (extract weight t).focus
      change (extract weight t).tree.erase.size = _ at partition
      rw [HeavyPath.Results.extract_tree] at partition
      obtain ⟨endpoint, focus⟩ := terminal
      rw [focus] at partition
      simp only [LabelledTree.erase, Tree.size, Nat.zero_add, Nat.add_zero] at partition
      change (Stacks.buildWith weight payload (extract weight t).context Stacks.empty).potential +
        (es.map Entry.credit).sum ≤ 23 * t.erase.size
      simp only [es, entriesOf, List.map_map, Function.comp_def]
      change (Stacks.buildWith weight payload (extract weight t).context Stacks.empty).potential +
        ((extract weight t).context.map credits).sum ≤ 23 * t.erase.size
      omega

/-- Forget the startup bound when only a recursive history witness is needed. -/
theorem of_canonical {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree}
    (layout : Recursive.Layout weight t shape) : ∃ credit, Layout weight t shape credit := by
  obtain ⟨credit, history, _⟩ := of_canonical_bounded layout
  exact ⟨credit, history⟩

theorem rebuild_history_bounded {α : Type} {weight : α → ℝ} {t : LabelledTree α} (positive : Positive weight t) :
    ∃ credit, Layout weight t (rebuild weight t) credit ∧ credit ≤ 23 * t.erase.size :=
  of_canonical_bounded (Recursive.Results.rebuild_layout positive)

theorem rebuild_history {α : Type} {weight : α → ℝ} {t : LabelledTree α} (positive : Positive weight t) :
    ∃ credit, Layout weight t (rebuild weight t) credit :=
  of_canonical (Recursive.Results.rebuild_layout positive)

end RotationBST.HeavyPath.Recursive.History
