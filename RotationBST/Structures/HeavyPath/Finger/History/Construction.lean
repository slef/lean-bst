module

public import RotationBST.Structures.HeavyPath.Finger.History.InitialPotential
public import RotationBST.Structures.HeavyPath.Recursive.History.Construction
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History
open Paired Recursive LabelledCursor Recursive.History

private theorem canonical_slots {α : Type} (weight : α → ℝ) (boundary : LabelledTree α)
    (carry : ℝ) (es : List (Entry α))
    (shapes : ∀ e ∈ es, e.shape = rebuild weight (framePayload e.source)) :
    sideSlots weight boundary (rebuild weight boundary) carry es =
      Finger.sideSlots weight (rebuild weight) boundary carry (es.map Entry.source) := by
  induction es generalizing carry with
  | nil => rfl
  | cons e es ih =>
    simp only [sideSlots, Finger.sideSlots, List.map_cons, shapes e (by simp)]
    rw [ih _ (fun f hf => shapes f (by simp [hf]))]

/-- The canonical inverted constructor supplies a complete occurrence state. -/
theorem build_state_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ s : State α, Valid weight cs left key right s ∧ s.pair = build weight cs left right ∧
      s.potential ≤ 23 * (plug cs (.node left key right)).erase.size := by
  classical
  have focus := (context_positive cs (.node left key right) positive).1
  obtain ⟨leftCredit, leftLayout, leftBound⟩ := rebuild_history_bounded focus.1
  obtain ⟨rightCredit, rightLayout, rightBound⟩ := rebuild_history_bounded focus.2.2
  have histories : ∀ f ∈ cs, ∃ credit,
      Recursive.History.Layout weight (framePayload f) (rebuild weight (framePayload f)) credit ∧
      credit ≤ 23 * (framePayload f).erase.size := by
    intro f hf
    exact rebuild_history_bounded (payload_positive cs _ positive hf)
  let credits : Frame α → Nat := fun f => if h : f ∈ cs then Classical.choose (histories f h) else 0
  let es : List (Entry α) := cs.map (fun f => ⟨f, rebuild weight (framePayload f), credits f⟩)
  let s : State α := ⟨es, rebuild weight left, rebuild weight right, leftCredit, rightCredit,
    build weight cs left right⟩
  have context : es.map Entry.source = cs := by simp [es, List.map_map, Function.comp_def]
  have shapes : ∀ e ∈ es, e.shape = rebuild weight (framePayload e.source) := by
    intro e he
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp he
    rfl
  have fringe := build_valid_fringe positive
  refine ⟨s, ⟨positive, context, fringe.1, leftLayout, rightLayout, ?_, ?_, ?_⟩, rfl, ?_⟩
  · intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    change Recursive.History.Layout weight (framePayload f) (rebuild weight (framePayload f)) (credits f)
    simp only [credits, dite_eq_left hf]
    exact (Classical.choose_spec (histories f hf)).1
  · change (build weight cs left right).lower.decode.mirror.fringe =
      sideSlots weight left (rebuild weight left) 0 (Recursive.History.lower es)
    rw [canonical_slots _ _ _ _ (fun e he => shapes e (lower_mem he)), lower_sources, context]
    exact fringe.2.1
  · change (build weight cs left right).upper.decode.fringe =
      (sideSlots weight right (rebuild weight right) 0 (Recursive.History.upper es).reverse).reverse
    rw [canonical_slots _ _ _ _ (fun e he => shapes e (upper_mem (List.mem_reverse.mp he))),
      List.map_reverse, upper_sources, context]
    exact fringe.2.2
  · have bounds : ∀ f ∈ cs, credits f ≤ 23 * (framePayload f).erase.size := by
      intro f hf
      simp only [credits, dite_eq_left hf]
      exact (Classical.choose_spec (histories f hf)).2
    have summed := sum_credits_bound cs credits 23 bounds
    have outer := canonical_pair_potential positive
    have partition := context_size α cs (.node left key right)
    simp only [LabelledTree.erase, Tree.size] at partition
    change (build weight cs left right).potential + leftCredit + rightCredit +
      (es.map Entry.credit).sum ≤ _
    simp only [es, List.map_map, Function.comp_def]
    change (build weight cs left right).potential + leftCredit + rightCredit +
      (cs.map credits).sum ≤ 23 * (plug cs (.node left key right)).erase.size
    omega

/-- Preserve the original constructor interface while retaining its stronger
startup certificate internally. -/
theorem build_state {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ s : State α, Valid weight cs left key right s ∧ s.pair = build weight cs left right := by
  obtain ⟨s, valid, pair, _⟩ := build_state_bounded positive
  exact ⟨s, valid, pair⟩

/-- The initial physical trace and every nested credit share a linear budget. -/
theorem state_initialization_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ (s : State α) (cost : Nat), Valid weight cs left key right s ∧
      Pointer.Trace ⟨(plug cs (.node left key right)).erase, []⟩ ⟨s.pair.tree, []⟩ cost ∧
      cost ≤ 16 * (plug cs (.node left key right)).erase.size ∧
      s.potential ≤ 23 * (plug cs (.node left key right)).erase.size ∧
      cost + s.potential ≤ 39 * (plug cs (.node left key right)).erase.size := by
  obtain ⟨s, valid, pair, potentialBound⟩ := build_state_bounded positive
  obtain ⟨cost, bound, trace⟩ := build_initialization positive
  refine ⟨s, cost, valid, ?_, bound, potentialBound, by omega⟩
  simpa only [pair] using trace

theorem state_initialization {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ (s : State α) (cost : Nat), Valid weight cs left key right s ∧
      Pointer.Trace ⟨(plug cs (.node left key right)).erase, []⟩ ⟨s.pair.tree, []⟩ cost ∧
      cost ≤ 16 * (plug cs (.node left key right)).erase.size := by
  obtain ⟨s, cost, valid, trace, bound, _, _⟩ := state_initialization_bounded positive
  exact ⟨s, cost, valid, trace, bound⟩

end RotationBST.HeavyPath.Finger.History
