module

public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Changes
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SDiff
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Transitions

/-- A local rewrite can introduce only its new parent or its two children.
The bound also holds for lists with duplicates or without a cut invariant. -/
theorem Step.introductions {roots next : List Component} {event : Event}
    (step : Step roots event next) :
    (next.toFinset \ roots.toFinset).card ≤ event.introduced := by
  classical
  cases step with
  | split before after lo l r =>
    have subset :
        ((before ++ [Component.mk lo l, Component.mk (lo + leaves l) r] ++ after).toFinset \
          (before ++ [Component.mk lo (.node l r)] ++ after).toFinset) ⊆
          {Component.mk lo l, Component.mk (lo + leaves l) r} := by
      intro c hc
      simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have count := (Finset.card_le_card subset).trans (Finset.card_insert_le _ _)
    simpa only [Finset.card_singleton, Event.introduced] using count
  | merge before after lo l r =>
    have subset :
        ((before ++ [Component.mk lo (.node l r)] ++ after).toFinset \
          (before ++ [Component.mk lo l, Component.mk (lo + leaves l) r] ++ after).toFinset) ⊆
          {Component.mk lo (.node l r)} := by
      intro c hc
      simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      simp only [Finset.mem_singleton]
      tauto
    simpa only [Finset.card_singleton, Event.introduced] using Finset.card_le_card subset

/-- New roots at the endpoint have births somewhere along the actual trace. -/
theorem Trace.introductions {roots next : List Component} {events : List Event}
    (trace : Trace roots events next) :
    (next.toFinset \ roots.toFinset).card ≤ introductions events := by
  classical
  induction trace with
  | nil => simp
  | @cons roots middle next event events step rest ih =>
    have subset : next.toFinset \ roots.toFinset ⊆
        (next.toFinset \ middle.toFinset) ∪ (middle.toFinset \ roots.toFinset) := by
      intro c hc
      obtain ⟨member, absent⟩ := Finset.mem_sdiff.mp hc
      by_cases mid : c ∈ middle.toFinset
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨mid, absent⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨member, mid⟩)
    have count := (Finset.card_le_card subset).trans (Finset.card_union_le _ _)
    have first := step.introductions
    change (next.toFinset \ roots.toFinset).card ≤
      event.introduced + Transitions.introductions events
    have restBound : (next.toFinset \ middle.toFinset).card ≤ Transitions.introductions events := ih
    omega

/-- Each event introduces at most two roots. The finer trace bound retains
one root per merge, leaving room for the item-potential merge charge. -/
theorem introductions_le (events : List Event) : introductions events ≤ 2 * events.length := by
  induction events with
  | nil => simp [introductions]
  | cons event events ih =>
    have eventBound : event.introduced ≤ 2 := by cases event <;> simp [Event.introduced]
    simp only [introductions, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- Root births and the merge-only item allowance share exactly two units
per event. Multiplying by twelve yields the paper's 24-unit step budget. -/
theorem introductions_merges (events : List Event) :
    introductions events + merges events = 2 * events.length := by
  induction events with
  | nil => simp [introductions, merges]
  | cons event events ih =>
    cases event <;> simp only [introductions, merges, List.map_cons, List.sum_cons,
      List.countP_cons, Event.introduced, Event.isMerge, Bool.false_eq_true,
      ite_false, ite_true, List.length_cons] at ih ⊢ <;> omega

end RotationBST.Geometric.GreedyASS.Reference.Transitions
