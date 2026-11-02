module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.AbstractBridge
public import RotationBST.Arboral.Online.LastTouch.Results.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Results.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Embedding.Results.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Layer.Results.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Ranks.Results.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Create.Results.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Nested.Results.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Assembly.Results.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Extraction.Results.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Rebuild.Results.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Transition.Results.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Simulation.Results.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Policy.Results.Abstract
public import RotationBST.Arboral.Online.Split.Abstract

@[expose] public section
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

/-- Online row cost is exactly the cardinality of the resulting ASS solution. -/
theorem online_solution {n : Nat} (A : OnlineAlgorithm n) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < n) :
    ∃ E : Offline n xs, E.points = fill A.step 0 ∅ xs ∧
      E.points.card = rowCost A.step 0 ∅ xs := offline_of_online A xs valid

/-- Every online geometric algorithm has one causal BST policy, valid from
all initial shapes, with constant rotation cost per added point and a linear
initialization allowance. The policy is fixed before the request sequence. -/
theorem online_bst (n : Nat) (A : OnlineAlgorithm n) :
    ∃ algorithm : Algorithm, ∀ tree : Tree, tree.size = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        algorithm.cost tree xs ≤ 6018 * rowCost A.step 0 ∅ xs + 6018 * n :=
  Online.Supernode.uniform_online_policy n A

/-- Conversely, an offline ASS solution can be revealed in legal rows.
The choice of those rows may depend on the future. -/
theorem offline_row {n time request : Nat} {P : Finset Point}
    (bounded : ∀ p ∈ P, p.1 < n) (satisfied : ASS P) (req : (request, time) ∈ P) :
    Completion n time request (pastPoints P time) (keysAt P time) :=
  offline_completion bounded satisfied req

theorem offline_cost {n : Nat} {xs : List Nat} (E : Offline n xs) :
    scheduleCost E.points xs.length = E.points.card := bounded_schedule_cost E.bounded

/-- A minimum offline geometric solution exists for every valid sequence. -/
theorem optimal_exists {n : Nat} (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    ∃ E : Offline n xs, ∀ F : Offline n xs, E.points.card ≤ F.points.card :=
  offline_minimum xs valid

theorem request_lower_bound {n : Nat} {xs : List Nat} (E : Offline n xs) :
    xs.length ≤ E.points.card := offline_lower_bound E

/-- The geometric view of rooted touches in a fixed BST is ASS. -/
theorem fixed_tree_view (t : Tree) (lo : Nat) (P : Finset Point)
    (rooted : RootedRows t lo P) : ASS P := rootedRows_ass t lo P rooted

end RotationBST.Arboral.Results

#check_bst_abstract RotationBST.Arboral.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Definitions.Abstract,
  RotationBST.Arboral.Online.Abstract, RotationBST.Arboral.Offline.Abstract,
  RotationBST.Arboral.Static.Abstract, RotationBST.Online.Abstract]
