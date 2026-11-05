module

public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Admissible
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Transitions

theorem contains_split (lo : Nat) (l r : Tree) (x : Nat) :
    (⟨lo, .node l r⟩ : Component).Contains x ↔
      (⟨lo, l⟩ : Component).Contains x ∨ (⟨lo + leaves l, r⟩ : Component).Contains x := by
  simp only [Component.Contains, Component.last, leaves]
  omega

private theorem split_ordered (before after : List Component) (lo : Nat) (l r : Tree) :
    (before ++ [Component.mk lo (.node l r)] ++ after).Pairwise (fun a b => a.last ≤ b.first) ↔
      (before ++ [Component.mk lo l, Component.mk (lo + leaves l) r] ++ after).Pairwise
        (fun a b => a.last ≤ b.first) := by
  simp [List.pairwise_append, List.pairwise_cons, Component.last, leaves]
  grind

theorem Step.ordered {a b : List Component} {event : Event} (step : Step a event b) :
    a.Pairwise (fun c d => c.last ≤ d.first) ↔ b.Pairwise (fun c d => c.last ≤ d.first) := by
  cases step with
  | split before after lo l r => exact split_ordered before after lo l r
  | merge before after lo l r => exact (split_ordered before after lo l r).symm

private theorem split_covers (before after : List Component) (lo : Nat) (l r : Tree) (x : Nat) :
    (∃ c ∈ before ++ [⟨lo, .node l r⟩] ++ after, c.Contains x) ↔
      ∃ c ∈ before ++ [⟨lo, l⟩, ⟨lo + leaves l, r⟩] ++ after, c.Contains x := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_and_right, exists_or, exists_eq_left, contains_split]

theorem Step.covers {a b : List Component} {event : Event} (step : Step a event b) (x : Nat) :
    (∃ c ∈ a, c.Contains x) ↔ ∃ c ∈ b, c.Contains x := by
  cases step with
  | split before after lo l r => exact split_covers before after lo l r x
  | merge before after lo l r => exact (split_covers before after lo l r x).symm

theorem Step.occurs {t : Tree} {lo : Nat} {a b : List Component} {event : Event}
    (step : Step a event b) (admissible : Admissible t lo event)
    (occurs : ∀ c ∈ a, ∃ k, Distance.Occurs t lo c k) :
    ∀ c ∈ b, ∃ k, Distance.Occurs t lo c k := by
  obtain ⟨k, parent⟩ := admissible
  cases step with
  | split before after first l r =>
    intro c member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (member | rfl | rfl) | member
    · exact occurs c (List.mem_append_left _ (List.mem_append_left _ member))
    · exact ⟨k + 1, occurs_trans parent (Distance.Occurs.left (.root l first))⟩
    · exact ⟨k + 1, occurs_trans parent (Distance.Occurs.right (.root r (first + leaves l)))⟩
    · exact occurs c (List.mem_append_right _ member)
  | merge before after first l r =>
    intro c member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with (member | rfl) | member
    · exact occurs c (List.mem_append_left _ (List.mem_append_left _ member))
    · exact ⟨k, parent⟩
    · exact occurs c (List.mem_append_right _ member)

theorem Step.cut {t : Tree} {lo : Nat} {a b : List Component} {event : Event}
    (step : Step a event b) (admissible : Admissible t lo event) (cut : Cut t lo a) :
    Cut t lo b :=
  ⟨step.ordered.mp cut.ordered, step.occurs admissible cut.occurs,
    fun x valid => (step.covers x).mp (cut.covers x valid)⟩

theorem Trace.cut {t : Tree} {lo : Nat} {a b : List Component} {events : List Event}
    (trace : Trace a events b) (admissible : ∀ e ∈ events, Admissible t lo e)
    (cut : Cut t lo a) : Cut t lo b := by
  induction trace with
  | nil => exact cut
  | cons step rest ih =>
    exact ih (fun e member => admissible e (List.mem_cons_of_mem _ member))
      (step.cut (admissible _ (by simp)) cut)

theorem forest_cut (t : Tree) (lo searched : Nat) : Cut t lo (forest t lo searched) :=
  ⟨Reference.ordered t lo searched, fun _ member => Distance.forest_occurs t lo searched member,
    Reference.covers t lo searched⟩

/-- Any prefix of the generated transition retains an ordered, covering
partition whose roots all occur in the original reference tree. -/
theorem plan_prefix_cut (t : Tree) (lo old new : Nat) {initial remaining : List Event}
    {roots : List Component} (events : plan t lo old new = initial ++ remaining)
    (trace : Trace (forest t lo old) initial roots) : Cut t lo roots := by
  apply trace.cut _ (forest_cut t lo old)
  intro event member
  apply plan_admissible t lo old new event
  rw [events]
  exact List.mem_append_left _ member

end RotationBST.Geometric.GreedyASS.Reference.Transitions
