module

public import RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.Steps
public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Introductions
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseOne
open Items Reference

/-- Item-potential increases telescope through actual intermediate cuts;
only merge events consume credit. -/
theorem trace_total (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point}
    (satisfied : ASS P) (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t)
    {roots next : List Component} {events : List Transitions.Event}
    (trace : Transitions.Trace roots events next) (cut : Transitions.Cut t lo roots)
    (admissible : ∀ e ∈ events, Transitions.Admissible t lo e) (domain : Finset Nat) :
    totalAt t lo searches P next domain ≤ totalAt t lo searches P roots domain + 12 * Transitions.merges events := by
  induction trace with
  | nil => simp [Transitions.merges]
  | @cons roots middle next event events step rest ih =>
    have first := step_total t lo searches satisfied valid cut step (admissible event (by simp)) domain
    have nextCut := step.cut (admissible event (by simp)) cut
    have remaining := ih nextCut (fun e he => admissible e (List.mem_cons_of_mem _ he))
    cases event <;>
      simp only [Transitions.merges, List.countP_cons, Transitions.Event.isMerge,
        Bool.false_eq_true, ite_false, ite_true] at first remaining ⊢ <;> omega

/-- The concrete forest plan connects the old potential to the next
intermediate potential, with twelve units per merge and no other item gain. -/
theorem plan_items (t : Tree) (lo : Nat) (prior : List Nat) (old next : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n (prior.length + 1) P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) (domain : Finset Nat) :
    totalAmount t lo ((prior ++ [old]) ++ [next]) P domain ≤
      totalAmount t lo (prior ++ [old]) P domain + 12 * Transitions.merges (Transitions.plan t lo old next) := by
  have bound := trace_total t lo (prior ++ [old]) satisfied valid
    (Transitions.plan_trace t lo old next) (Transitions.forest_cut t lo old)
    (Transitions.plan_admissible t lo old next) domain
  have oldHistory : History n (prior ++ [old]).length P := by simpa only [List.length_append, List.length_singleton] using history
  rw [total_initial t lo prior old history valid domain, total_final t lo (prior ++ [old]) next oldHistory valid domain] at bound
  exact bound

end RotationBST.Geometric.GreedyASS.Potential.PhaseOne
