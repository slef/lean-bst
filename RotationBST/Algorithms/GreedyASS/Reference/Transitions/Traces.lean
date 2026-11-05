module

public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Transitions

theorem Step.inverse {a b : List Component} {event : Event} (step : Step a event b) :
    Step b event.inverse a := by
  cases step with
  | split before after lo l r => exact .merge before after lo l r
  | merge before after lo l r => exact .split before after lo l r

theorem Step.context {a b : List Component} {event : Event} (step : Step a event b)
    (before after : List Component) : Step (before ++ a ++ after) event (before ++ b ++ after) := by
  cases step with
  | split first last lo l r =>
    simpa only [List.append_assoc] using Step.split (before ++ first) (last ++ after) lo l r
  | merge first last lo l r =>
    simpa only [List.append_assoc] using Step.merge (before ++ first) (last ++ after) lo l r

theorem Trace.append {a b c : List Component} {xs ys : List Event}
    (first : Trace a xs b) (last : Trace b ys c) : Trace a (xs ++ ys) c := by
  induction first with
  | nil => exact last
  | cons step rest ih => exact .cons step (ih last)

theorem Trace.context {a b : List Component} {events : List Event} (trace : Trace a events b)
    (before after : List Component) : Trace (before ++ a ++ after) events (before ++ b ++ after) := by
  induction trace with
  | nil => exact .nil _
  | cons step rest ih => exact .cons (step.context before after) ih

theorem Trace.split {a b : List Component} {xs ys : List Event}
    (trace : Trace a (xs ++ ys) b) : ∃ middle, Trace a xs middle ∧ Trace middle ys b := by
  induction xs generalizing a with
  | nil => exact ⟨a, .nil _, trace⟩
  | cons event xs ih =>
    cases trace with
    | cons step rest =>
      obtain ⟨middle, first, last⟩ := ih rest
      exact ⟨middle, .cons step first, last⟩

theorem Trace.inverse {a b : List Component} {events : List Event} (trace : Trace a events b) :
    Trace b (events.reverse.map Event.inverse) a := by
  induction trace with
  | nil => exact .nil _
  | cons step rest ih =>
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil] using
      ih.append (Trace.cons step.inverse (Trace.nil _))

theorem descend_trace (t : Tree) (lo searched : Nat) :
    Trace [⟨lo, t⟩] (descend t lo searched) (forest t lo searched) := by
  induction t generalizing lo with
  | nil => exact .nil _
  | node l r il ir =>
    have split : Step [⟨lo, .node l r⟩] (.split lo l r) [⟨lo, l⟩, ⟨lo + leaves l, r⟩] :=
      Step.split [] [] lo l r
    by_cases left : searched < lo + leaves l
    · simpa only [descend, forest, ite_eq_left left, List.nil_append, List.append_nil,
        List.singleton_append] using Trace.cons split ((il lo).context [] [⟨lo + leaves l, r⟩])
    · simpa only [descend, forest, ite_eq_right left, List.nil_append, List.append_nil,
        List.singleton_append] using Trace.cons split ((ir (lo + leaves l)).context [⟨lo, l⟩] [])

theorem ascend_trace (t : Tree) (lo searched : Nat) :
    Trace (forest t lo searched) (ascend t lo searched) [⟨lo, t⟩] :=
  (descend_trace t lo searched).inverse

theorem plan_trace (t : Tree) (lo old new : Nat) :
    Trace (forest t lo old) (plan t lo old new) (forest t lo new) := by
  induction t generalizing lo with
  | nil => exact .nil _
  | node l r il ir =>
    by_cases left : old < lo + leaves l ∧ new < lo + leaves l
    · simpa only [plan, ite_eq_left left, forest, ite_eq_left left.1, ite_eq_left left.2,
        List.nil_append] using (il lo).context [] [⟨lo + leaves l, r⟩]
    · by_cases right : lo + leaves l ≤ old ∧ lo + leaves l ≤ new
      · have oldRight := Nat.not_lt.mpr right.1
        have newRight := Nat.not_lt.mpr right.2
        simpa only [plan, ite_eq_right left, ite_eq_left right, forest,
          ite_eq_right oldRight, ite_eq_right newRight, List.append_nil, List.singleton_append] using
          (ir (lo + leaves l)).context [⟨lo, l⟩] []
      · simpa only [plan, ite_eq_right left, ite_eq_right right] using
          (ascend_trace (.node l r) lo old).append (descend_trace (.node l r) lo new)

end RotationBST.Geometric.GreedyASS.Reference.Transitions
