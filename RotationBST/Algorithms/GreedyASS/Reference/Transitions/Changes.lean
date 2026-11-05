module

public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Partition
public import RotationBST.Algorithms.GreedyASS.Reference.Distance.Components
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Transitions

private theorem split_distance (before after : List Component) (lo x : Nat) (l r : Tree)
    {a b : Component}
    (ordered : (before ++ [Component.mk lo l, Component.mk (lo + leaves l) r] ++ after).Pairwise
      (fun c d => c.last ≤ d.first))
    (ha : a ∈ before ++ [Component.mk lo (.node l r)] ++ after)
    (hb : b ∈ before ++ [Component.mk lo l, Component.mk (lo + leaves l) r] ++ after)
    (ca : a.Contains x) (cb : b.Contains x) :
    Distance.toRoot b x ≤ Distance.toRoot a x ∧
      Distance.toRoot a x ≤ Distance.toRoot b x + 1 := by
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · have ha' : a ∈ before ++ [Component.mk lo l, Component.mk (lo + leaves l) r] ++ after :=
        List.mem_append_left _ (List.mem_append_left _ ha)
      have same := unique_of_ordered _ ordered ha' hb ca cb
      subst b
      omega
    · have same := List.mem_singleton.mp ha
      subst a
      rcases (contains_split lo l r x).mp ca with left | right
      · have member : Component.mk lo l ∈
            before ++ [Component.mk lo l, Component.mk (lo + leaves l) r] ++ after := by simp
        have same := unique_of_ordered _ ordered member hb left cb
        subst b
        have distance := Distance.merge_left l r lo x left
        omega
      · have member : Component.mk (lo + leaves l) r ∈
            before ++ [Component.mk lo l, Component.mk (lo + leaves l) r] ++ after := by simp
        have same := unique_of_ordered _ ordered member hb right cb
        subst b
        have distance := Distance.merge_right l r lo x right
        omega
  · have ha' : a ∈ before ++ [Component.mk lo l, Component.mk (lo + leaves l) r] ++ after :=
      List.mem_append_right _ ha
    have same := unique_of_ordered _ ordered ha' hb ca cb
    subst b
    omega

/-- A split can only decrease root distance, by at most one; a merge can
only increase it, by at most one. Components outside the event keep their distance. -/
theorem Step.distance {roots next : List Component} {event : Event}
    (step : Step roots event next)
    (oldOrdered : roots.Pairwise (fun c d => c.last ≤ d.first))
    {a b : Component} {x : Nat} (ha : a ∈ roots) (hb : b ∈ next)
    (ca : a.Contains x) (cb : b.Contains x) :
    match event with
    | .split _ _ _ => Distance.toRoot b x ≤ Distance.toRoot a x ∧
        Distance.toRoot a x ≤ Distance.toRoot b x + 1
    | .merge _ _ _ => Distance.toRoot a x ≤ Distance.toRoot b x ∧
        Distance.toRoot b x ≤ Distance.toRoot a x + 1 := by
  have nextOrdered := step.ordered.mp oldOrdered
  cases step with
  | split before after lo l r => exact split_distance before after lo x l r nextOrdered ha hb ca cb
  | merge before after lo l r => exact split_distance before after lo x l r oldOrdered hb ha cb ca

/-- Each local rewrite changes a key's root distance by at most one. -/
theorem Step.distance_bound {roots next : List Component} {event : Event}
    (step : Step roots event next)
    (oldOrdered : roots.Pairwise (fun c d => c.last ≤ d.first))
    {a b : Component} {x : Nat} (ha : a ∈ roots) (hb : b ∈ next)
    (ca : a.Contains x) (cb : b.Contains x) :
    Distance.toRoot b x ≤ Distance.toRoot a x + 1 ∧
      Distance.toRoot a x ≤ Distance.toRoot b x + 1 := by
  have bound := step.distance oldOrdered ha hb ca cb
  cases event <;> simp only at bound <;> omega

/-- The same ordered partition exists at every event boundary, including
when a transition is interrupted strictly between its merge and split phases. -/
theorem plan_prefix (t : Tree) (lo old new : Nat) (initial remaining : List Event)
    (events : plan t lo old new = initial ++ remaining) :
    ∃ roots, Trace (forest t lo old) initial roots ∧
      Trace roots remaining (forest t lo new) ∧ Cut t lo roots := by
  have full := plan_trace t lo old new
  rw [events] at full
  obtain ⟨roots, first, last⟩ := full.split
  exact ⟨roots, first, last, plan_prefix_cut t lo old new events first⟩

theorem Cut.partition {t : Tree} {lo : Nat} {roots : List Component} (cut : Cut t lo roots)
    {x : Nat} (valid : lo ≤ x ∧ x < lo + leaves t) :
    ∃! c, c ∈ roots ∧ c.Contains x := by
  obtain ⟨c, member, inside⟩ := cut.covers x valid
  exact ⟨c, ⟨member, inside⟩, fun d hd =>
    unique_of_ordered roots cut.ordered hd.1 member hd.2 inside⟩

/-- Root-distance changes accumulate along the actual local-event trace. -/
theorem Trace.distance_bound {t : Tree} {lo x : Nat} {roots next : List Component}
    {events : List Event} (trace : Trace roots events next)
    (admissible : ∀ e ∈ events, Admissible t lo e) (cut : Cut t lo roots)
    (valid : lo ≤ x ∧ x < lo + leaves t) {a b : Component}
    (ha : a ∈ roots) (hb : b ∈ next) (ca : a.Contains x) (cb : b.Contains x) :
    Distance.toRoot b x ≤ Distance.toRoot a x + events.length ∧
      Distance.toRoot a x ≤ Distance.toRoot b x + events.length := by
  induction trace generalizing a with
  | nil =>
    have same := unique_of_ordered _ cut.ordered ha hb ca cb
    subst b
    simp
  | @cons roots middle next event events step rest ih =>
    have middleCut := step.cut (admissible event (by simp)) cut
    obtain ⟨c, hc, cc⟩ := middleCut.covers x valid
    have first := step.distance_bound cut.ordered ha hc ca cc
    have last := ih (fun e member => admissible e (List.mem_cons_of_mem _ member))
      middleCut hc hb cc
    simp only [List.length_cons]
    omega

end RotationBST.Geometric.GreedyASS.Reference.Transitions
