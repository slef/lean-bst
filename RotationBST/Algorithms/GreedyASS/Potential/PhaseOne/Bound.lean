module

public import RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.Trace
public import RotationBST.Algorithms.GreedyASS.Virgin.Transitions
public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.History
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseOne
open Items Reference

/-- Lemma 3.3 in additive form, with the paper's 24 units per reference
edge. The point set is fixed while its reference history advances. -/
theorem step (t : Tree) (lo : Nat) (prior : List Nat) (old next : Nat)
    (valid : ∀ x ∈ (prior ++ [old]) ++ [next], lo ≤ x ∧ x < lo + leaves t) (domain : Finset Nat) :
    totalAmount t lo ((prior ++ [old]) ++ [next]) (Virgin.points (prior ++ [old])) domain +
        Virgin.before t lo (prior ++ [old]) next ≤
      totalAmount t lo (prior ++ [old]) (Virgin.points (prior ++ [old])) domain +
        Virgin.after t lo prior old + 24 * Transitions.edges t lo old next := by
  have oldValid : ∀ x ∈ prior ++ [old], x < lo + leaves t :=
    fun x hx => (valid x (List.mem_append_left _ hx)).2
  have history : History (lo + leaves t) (prior.length + 1) (Virgin.points (prior ++ [old])) := by
    simpa only [List.length_append, List.length_singleton] using Virgin.points_history _ (prior ++ [old]) oldValid
  have pointValid := Unaccessed.points_property _ (prior ++ [old])
    (fun x hx => valid x (List.mem_append_left _ hx))
  have items := plan_items t lo prior old next (Unaccessed.points_satisfied _ oldValid) history pointValid domain
  have virgin := Virgin.merge_budget t lo prior old next
  omega

end RotationBST.Geometric.GreedyASS.Potential.PhaseOne
