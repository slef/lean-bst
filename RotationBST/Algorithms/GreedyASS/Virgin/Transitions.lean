module

public import RotationBST.Algorithms.GreedyASS.Virgin.Potential
public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Introductions
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Virgin
open Reference

/-- A root that survives the forest change keeps exactly its post-access
non-virgin status. The preceding row has already been accounted for. -/
theorem survives (t : Tree) (lo : Nat) (history : List Nat) (old new : Nat) {c : Component}
    (oldRoot : c ∈ forest t lo old) (newRoot : c ∈ forest t lo new) :
    NonVirgin t lo (history ++ [old]) new c ↔ NonVirgin t lo (history ++ [old]) old c := by
  rw [advance, advance]
  simp only [oldRoot, newRoot, true_and]

/-- A new virgin root either was already virgin after the previous row or
was introduced by the forest change. Surviving non-virgins are never reset. -/
theorem roots_transition (t : Tree) (lo : Nat) (history : List Nat) (old new : Nat) :
    roots t lo (history ++ [old]) new ⊆ roots t lo (history ++ [old]) old ∪
      ((forest t lo new).toFinset \ (forest t lo old).toFinset) := by
  classical
  intro c hc
  obtain ⟨newRoot, virgin⟩ := Finset.mem_filter.mp hc
  have newMember := List.mem_toFinset.mp newRoot
  by_cases oldMember : c ∈ forest t lo old
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr oldMember,
      fun nonvirgin => virgin ((survives t lo history old new oldMember newMember).mpr nonvirgin)⟩
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨newRoot, fun member => oldMember (List.mem_toFinset.mp member)⟩)

/-- The virgin part of Phase I costs at most twelve per actual root birth:
one for a merge and two for a split. This retains the merge budget needed
for the separate item-potential analysis. -/
theorem transition_bound (t : Tree) (lo : Nat) (history : List Nat) (old new : Nat)
    {events : List Transitions.Event}
    (trace : Transitions.Trace (forest t lo old) events (forest t lo new)) :
    before t lo (history ++ [old]) new ≤ after t lo history old + 12 * Transitions.introductions events := by
  classical
  have subset := roots_transition t lo history old new
  have cardinal := (Finset.card_le_card subset).trans (Finset.card_union_le _ _)
  have births := trace.introductions
  rw [roots_after] at cardinal
  unfold before after
  omega

/-- The LCA-routed reference-forest change has the same concrete bound. -/
theorem plan_bound (t : Tree) (lo : Nat) (history : List Nat) (old new : Nat) :
    before t lo (history ++ [old]) new ≤ after t lo history old +
      12 * Transitions.introductions (Transitions.plan t lo old new) :=
  transition_bound t lo history old new (Transitions.plan_trace t lo old new)

/-- A coarser edge-count form for the virgin contribution alone. Item
potential must still be included before claiming the paper's Phase I bound. -/
theorem path_bound (t : Tree) (lo : Nat) (history : List Nat) (old new : Nat) :
    before t lo (history ++ [old]) new ≤ after t lo history old + 24 * Transitions.edges t lo old new := by
  have bound := plan_bound t lo history old new
  have births := Transitions.introductions_le (Transitions.plan t lo old new)
  rw [Transitions.plan_length] at births
  omega

/-- The virgin contribution leaves twelve units per merge within the
24-per-edge Phase I budget. Those units remain to be justified by the
item-potential analysis; this theorem does not assume that analysis. -/
theorem merge_budget (t : Tree) (lo : Nat) (history : List Nat) (old new : Nat) :
    before t lo (history ++ [old]) new +
        12 * Transitions.merges (Transitions.plan t lo old new) ≤
      after t lo history old + 24 * Transitions.edges t lo old new := by
  have bound := plan_bound t lo history old new
  have budget := Transitions.introductions_merges (Transitions.plan t lo old new)
  rw [Transitions.plan_length] at budget
  omega

end RotationBST.Geometric.GreedyASS.Virgin
