module

public import RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Changes
public import RotationBST.Algorithms.GreedyASS.Potential.Forest
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseOne
open Items Reference

/-- Ordered cuts make the executable first-containing-component query
independent of where its unique witness occurs in the root list. -/
theorem rootBlue_component {roots : List Component}
    (ordered : roots.Pairwise (fun c d => c.last ≤ d.first)) {c : Component} {x : Nat}
    (member : c ∈ roots) (inside : c.Contains x) : rootBlue roots x = Distance.toRoot c x + 1 := by
  induction roots with
  | nil => simp at member
  | cons a roots ih =>
    by_cases contains : a.Contains x
    · have same := unique_of_ordered (a :: roots) ordered (List.mem_cons_self ..) member contains inside
      simp only [rootBlue, same, ite_eq_left inside]
    · have tail : c ∈ roots := by
        rcases List.mem_cons.mp member with rfl | hm
        · exact (contains inside).elim
        · exact hm
      simpa only [rootBlue, ite_eq_right contains] using ih (List.pairwise_cons.mp ordered).2 tail

theorem rootBlue_forest (t : Tree) (lo searched x : Nat) (valid : lo ≤ x ∧ x < lo + leaves t) :
    rootBlue (forest t lo searched) x = blue t lo searched x := by
  obtain ⟨c, member, inside⟩ := covers t lo searched x valid
  rw [rootBlue_component (Reference.ordered t lo searched) member inside,
    blue_component t lo searched x member inside]

/-- Numerical blue changes at a certified intermediate cut use the actual
component-root distance theorem for the split or merge. -/
theorem rootBlue_step {t : Tree} {lo x : Nat} {roots next : List Component} {event : Transitions.Event}
    (cut : Transitions.Cut t lo roots) (step : Transitions.Step roots event next)
    (admissible : Transitions.Admissible t lo event) (valid : lo ≤ x ∧ x < lo + leaves t) :
    match event with
    | .split _ _ _ => rootBlue next x ≤ rootBlue roots x
    | .merge _ _ _ => rootBlue next x ≤ rootBlue roots x + 1 := by
  have nextCut := step.cut admissible cut
  obtain ⟨a, ha, ca⟩ := cut.covers x valid
  obtain ⟨b, hb, cb⟩ := nextCut.covers x valid
  have bounds := step.distance cut.ordered ha hb ca cb
  rw [rootBlue_component cut.ordered ha ca, rootBlue_component nextCut.ordered hb cb]
  cases event <;> simp only at bounds ⊢ <;> omega

end RotationBST.Geometric.GreedyASS.Potential.PhaseOne
