module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.AbstractBridge

@[expose] public section

/-! The executable sweep is in `Algorithm/Abstract`. It is a legal online
geometric algorithm, and every legal completion of the current row contains
its points, so it is the unique minimum-cardinality completion of that row.
This local minimum is not a claim of global (dynamic) optimality. -/
namespace RotationBST.Arboral.Results

/-- The standard empty-rectangle sweep completes the current row. -/
theorem greedy_step {n time request : Nat} {P : Finset Point}
    (history : History n time P) (satisfied : ASS P) (valid : request < n) :
    Completion n time request P (greedySweep time request P) :=
  sweep_correct history satisfied valid

/-- GreedyASS is an online geometric algorithm; its input contains no future. -/
def greedyASS (n : Nat) : OnlineAlgorithm n where
  step := greedySweep
  correct := fun _ _ _ => greedy_step

/-- Every legal completion contains GreedyASS's points. -/
theorem greedy_required {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (legal : Completion n time request P keys) :
    greedySweep time request P ⊆ keys := sweep_subset history legal

/-- The minimum-cardinality completion is unique and equals the sweep. -/
theorem greedy_minimum {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (satisfied : ASS P) (valid : request < n) :
    GreedyRow n time request P keys ↔ keys = greedySweep time request P := by
  constructor
  · exact greedy_unique history satisfied valid
  · rintro rfl
    exact sweep_greedy history satisfied valid

end RotationBST.Arboral.Results

#check_bst_abstract RotationBST.Arboral.Results allowing [
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Algorithms.GreedyASS.Algorithm.Abstract]
