module

import RotationBST.Audit.Check
public import RotationBST.Models.Geometric.AbstractBridge

@[expose] public section

/-! Facts about the geometric model itself. The definitions are in
`Definitions/Abstract`, `Online/Abstract`, `Offline/Abstract`, and
`Static/Abstract`. GreedyASS is in `Algorithms/GreedyASS/Abstract`; the
correspondence with BST executions is in `Models/Equivalence/Abstract`. -/
namespace RotationBST.Arboral.Results

/-- Online row cost is exactly the cardinality of the resulting ASS solution. -/
theorem online_solution {n : Nat} (A : OnlineAlgorithm n) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < n) :
    ∃ E : Offline n xs, E.points = fill A.step 0 ∅ xs ∧
      E.points.card = rowCost A.step 0 ∅ xs := offline_of_online A xs valid

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

/-- Every solution contains the request points, so it has at least `m` points. -/
theorem request_lower_bound {n : Nat} {xs : List Nat} (E : Offline n xs) :
    xs.length ≤ E.points.card := offline_lower_bound E

/-- The geometric view of rooted touches in a fixed BST is ASS. -/
theorem fixed_tree_view (t : Tree) (lo : Nat) (P : Finset Point)
    (rooted : RootedRows t lo P) : ASS P := rootedRows_ass t lo P rooted

end RotationBST.Arboral.Results

#check_bst_abstract RotationBST.Arboral.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract, RotationBST.Models.Geometric.Offline.Abstract,
  RotationBST.Models.Geometric.Static.Abstract]
