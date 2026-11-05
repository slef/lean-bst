module

public import RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Algorithm.Abstract
public import RotationBST.Models.Geometric.Online.Abstract

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Virgin
open Reference

/-- The actual points produced by GreedyASS from the empty history. -/
def points (history : List Nat) : Finset Point := fill greedySweep 0 ∅ history

def keys (history : List Nat) (request : Nat) : Finset Nat :=
  greedySweep history.length request (points history)

/-- An earlier access occurred while this component was a root, and it has
remained a root at every intervening search, including the current one.
This is a proof observation, not extra state required by GreedyASS. -/
def NonVirgin (t : Tree) (lo : Nat) (history : List Nat) (request : Nat)
    (c : Component) : Prop :=
  ∃ before first after accessed,
    history = before ++ (first :: after) ∧
    accessed ∈ keys before first ∧ c.Contains accessed ∧
    ∀ x ∈ first :: (after ++ [request]), c ∈ forest t lo x

/-- Components touched by the current row, independently of their age. -/
noncomputable def touched (t : Tree) (lo : Nat) (history : List Nat) (request : Nat) :
    Finset Component := by
  classical
  exact (forest t lo request).toFinset.filter fun c => ∃ x ∈ keys history request, c.Contains x

noncomputable def oldTouched (t : Tree) (lo : Nat) (history : List Nat) (request : Nat) :
    Finset Component := by
  classical
  exact (touched t lo history request).filter (NonVirgin t lo history request)

/-- Virgin roots immediately before adding the current access row. -/
noncomputable def roots (t : Tree) (lo : Nat) (history : List Nat) (request : Nat) :
    Finset Component := by
  classical
  exact (forest t lo request).toFinset.filter fun c => ¬ NonVirgin t lo history request c

/-- Phase-II virgin potential; each untouched virgin root contributes 12. -/
noncomputable def before (t : Tree) (lo : Nat) (history : List Nat) (request : Nat) : Nat :=
  12 * (roots t lo history request).card

noncomputable def after (t : Tree) (lo : Nat) (history : List Nat) (request : Nat) : Nat :=
  12 * (roots t lo history request \ touched t lo history request).card

end RotationBST.Geometric.GreedyASS.Virgin
