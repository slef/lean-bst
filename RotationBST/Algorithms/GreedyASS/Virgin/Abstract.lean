module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Virgin.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Virgin.Results
open Reference

theorem initial (t : Tree) (lo request : Nat) (c : Component) :
    ¬ NonVirgin t lo [] request c := initially_virgin t lo request c

/-- Exact lifetime update, including loss of old status when a root disappears. -/
theorem lifetime (t : Tree) (lo : Nat) (history : List Nat) (request next : Nat) (c : Component) :
    NonVirgin t lo (history ++ [request]) next c ↔
      c ∈ forest t lo next ∧
        (NonVirgin t lo history request c ∨
          (c ∈ forest t lo request ∧ ∃ x ∈ keys history request, c.Contains x)) :=
  advance t lo history request next c

/-- An earlier access constrains the actual next GreedyASS row. -/
theorem barrier {t : Tree} {lo request : Nat} {history : List Nat} {c : Component}
    (valid : ∀ x ∈ history ++ [request], lo ≤ x ∧ x < lo + leaves t)
    (old : NonVirgin t lo history request c) :
    ∃ accessed, c.Contains accessed ∧
      ((∀ x ∈ keys history request, x ≤ accessed) ∨
        (∀ x ∈ keys history request, accessed ≤ x)) := old_barrier valid old

/-- Lemma 3.7, including searched singleton components. -/
theorem count (t : Tree) (lo : Nat) (history : List Nat) (request : Nat)
    (valid : ∀ x ∈ history ++ [request], lo ≤ x ∧ x < lo + leaves t) :
    (oldTouched t lo history request).card ≤ 2 := Virgin.count t lo history request valid

/-- The remaining virgin roots agree with the actual completed history. -/
theorem update (t : Tree) (lo : Nat) (history : List Nat) (request : Nat) :
    roots t lo (history ++ [request]) request =
      roots t lo history request \ touched t lo history request := roots_after t lo history request

theorem exact (t : Tree) (lo : Nat) (history : List Nat) (request : Nat) :
    before t lo history request = after t lo history request +
      12 * (roots t lo history request ∩ touched t lo history request).card :=
  exact_drop t lo history request

/-- Lemma 3.8, stated without truncated subtraction. -/
theorem decrease (t : Tree) (lo : Nat) (history : List Nat) (request : Nat)
    (valid : ∀ x ∈ history ++ [request], lo ≤ x ∧ x < lo + leaves t) :
    after t lo history request + 12 * (touched t lo history request).card ≤
      before t lo history request + 24 := Virgin.decrease t lo history request valid


/-- Surviving roots preserve their completed-row non-virgin status. -/
theorem survival (t : Tree) (lo : Nat) (history : List Nat) (old new : Nat) {c : Component}
    (oldRoot : c ∈ forest t lo old) (newRoot : c ∈ forest t lo new) :
    NonVirgin t lo (history ++ [old]) new c ↔ NonVirgin t lo (history ++ [old]) old c :=
  survives t lo history old new oldRoot newRoot

/-- Virgin potential increases by at most twelve per root introduction along a trace. -/
theorem transition (t : Tree) (lo : Nat) (history : List Nat) (old new : Nat)
    {events : List Transitions.Event}
    (trace : Transitions.Trace (forest t lo old) events (forest t lo new)) :
    before t lo (history ++ [old]) new ≤ after t lo history old + 12 * Transitions.introductions events :=
  transition_bound t lo history old new trace

/-- The concrete LCA-routed forest change has the root-introduction bound. -/
theorem forest_change (t : Tree) (lo : Nat) (history : List Nat) (old new : Nat) :
    before t lo (history ++ [old]) new ≤ after t lo history old +
      12 * Transitions.introductions (Transitions.plan t lo old new) :=
  plan_bound t lo history old new

/-- Virgin potential leaves twelve units per merge in the 24-per-edge budget; item changes are separate. -/
theorem phase_one_budget (t : Tree) (lo : Nat) (history : List Nat) (old new : Nat) :
    before t lo (history ++ [old]) new +
        12 * Transitions.merges (Transitions.plan t lo old new) ≤
      after t lo history old + 24 * Transitions.edges t lo old new :=
  merge_budget t lo history old new

end RotationBST.Geometric.GreedyASS.Virgin.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Virgin.Results`: 11 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Virgin.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Algorithms.GreedyASS.Algorithm.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Transitions.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Virgin.Definitions.Abstract]
