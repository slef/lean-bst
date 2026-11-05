module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Transitions.Results

/-- Splitting down one leaf path constructs its reference forest. -/
theorem descending (t : Tree) (lo searched : Nat) :
    Trace [⟨lo, t⟩] (descend t lo searched) (forest t lo searched) ∧
      (descend t lo searched).length = Distance.depth t lo searched ∧
      ∀ event ∈ descend t lo searched, Admissible t lo event :=
  ⟨descend_trace t lo searched, descend_length t lo searched, descend_admissible t lo searched⟩

theorem ascending (t : Tree) (lo searched : Nat) :
    Trace (forest t lo searched) (ascend t lo searched) [⟨lo, t⟩] ∧
      (ascend t lo searched).length = Distance.depth t lo searched ∧
      ∀ event ∈ ascend t lo searched, Admissible t lo event :=
  ⟨ascend_trace t lo searched, ascend_length t lo searched, ascend_admissible t lo searched⟩

/-- Merge to the LCA, then split toward the new search. Common ancestors
above the LCA are untouched. Every event belongs to the original tree. -/
theorem transition (t : Tree) (lo old new : Nat) :
    Trace (forest t lo old) (plan t lo old new) (forest t lo new) ∧
      (plan t lo old new).length = edges t lo old new ∧
      ∀ event ∈ plan t lo old new, Admissible t lo event :=
  ⟨plan_trace t lo old new, plan_length t lo old new, plan_admissible t lo old new⟩

/-- Exact edge accounting, expressed using the node-counted upward paths. -/
theorem path (t : Tree) (lo x y : Nat)
    (validX : lo ≤ x ∧ x < lo + leaves t) (validY : lo ≤ y ∧ y < lo + leaves t) :
    (plan t lo x y).length + 2 =
      Distance.toRoot (Distance.lca t lo x y) x + Distance.toRoot (Distance.lca t lo x y) y :=
  path_length t lo x y validX validY

theorem repeated (t : Tree) (lo x : Nat) : plan t lo x x = [] := plan_repeated t lo x

theorem preservation {t : Tree} {lo : Nat} {a b : List Component} {events : List Event}
    (trace : Trace a events b) (admissible : ∀ e ∈ events, Admissible t lo e)
    (cut : Cut t lo a) : Cut t lo b := trace.cut admissible cut

/-- Every event boundary has an actual intermediate partition and traces
realizing both the completed and remaining portions of the transition. -/
theorem intermediate (t : Tree) (lo old new : Nat) (initial remaining : List Event)
    (events : plan t lo old new = initial ++ remaining) :
    ∃ roots, Trace (forest t lo old) initial roots ∧
      Trace roots remaining (forest t lo new) ∧ Cut t lo roots :=
  plan_prefix t lo old new initial remaining events

theorem ownership {t : Tree} {lo : Nat} {roots : List Component} (cut : Cut t lo roots)
    {x : Nat} (valid : lo ≤ x ∧ x < lo + leaves t) :
    ∃! c, c ∈ roots ∧ c.Contains x := cut.partition valid

/-- Splits weakly decrease root distance; merges weakly increase it.
In either direction, the change is at most one. -/
theorem local_distance {roots next : List Component} {event : Event}
    (step : Step roots event next)
    (ordered : roots.Pairwise (fun c d => c.last ≤ d.first))
    {a b : Component} {x : Nat} (ha : a ∈ roots) (hb : b ∈ next)
    (ca : a.Contains x) (cb : b.Contains x) :
    match event with
    | .split _ _ _ => Distance.toRoot b x ≤ Distance.toRoot a x ∧
        Distance.toRoot a x ≤ Distance.toRoot b x + 1
    | .merge _ _ _ => Distance.toRoot a x ≤ Distance.toRoot b x ∧
        Distance.toRoot b x ≤ Distance.toRoot a x + 1 := step.distance ordered ha hb ca cb

theorem sequence_distance {t : Tree} {lo x : Nat} {roots next : List Component}
    {events : List Event} (trace : Trace roots events next)
    (admissible : ∀ e ∈ events, Admissible t lo e) (cut : Cut t lo roots)
    (valid : lo ≤ x ∧ x < lo + leaves t) {a b : Component}
    (ha : a ∈ roots) (hb : b ∈ next) (ca : a.Contains x) (cb : b.Contains x) :
    Distance.toRoot b x ≤ Distance.toRoot a x + events.length ∧
      Distance.toRoot a x ≤ Distance.toRoot b x + events.length :=
  trace.distance_bound admissible cut valid ha hb ca cb


/-- A split introduces at most two roots, and a merge at most one. -/
theorem local_roots {roots next : List Component} {event : Event} (step : Step roots event next) :
    (next.toFinset \ roots.toFinset).card ≤ event.introduced := step.introductions

/-- Endpoint roots absent initially are paid for by births along the trace. -/
theorem new_roots {roots next : List Component} {events : List Event} (trace : Trace roots events next) :
    (next.toFinset \ roots.toFinset).card ≤ introductions events := trace.introductions

/-- Exact sharing of the per-event budget between root births and merges. -/
theorem birth_budget (events : List Event) : introductions events + merges events = 2 * events.length :=
  introductions_merges events

end RotationBST.Geometric.GreedyASS.Reference.Transitions.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Reference.Transitions.Results`: 14 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Reference.Transitions.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Transitions.Definitions.Abstract]
