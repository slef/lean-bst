module

public import RotationBST.Algorithms.Tango.Auxiliary.Updates
public import RotationBST.Algorithms.Splay.Updates.Potential

@[expose] public section
namespace RotationBST.Geometric.Region
open Pointer.Lazy.Skeleton

theorem auxiliary_access_bound (s : Region) (x : Nat) (hx : x ∈ keys s 0) :
    ∃ u cost, s.fringe = u.fringe ∧ Access s.tree u.tree x cost ∧
      (cost : ℝ) + auxiliaryPotential u - auxiliaryPotential s ≤ 3 * Real.logb 2 s.size + 1 := by
  obtain ⟨u, hu, hf, access⟩ := auxiliary_splay s x hx
  have bound := Splay.Updates.unit_access (shape s) (index s 0 x)
    (by rw [shape_size]; exact index_valid hx)
  refine ⟨u, _, hf, access, ?_⟩
  simpa only [← hu, Splay.Updates.unitPotential, auxiliaryPotential, shape_size] using bound

theorem auxiliary_split_bound (s : Region) (k : Nat) (positive : 0 < k) (valid : k ≤ s.size) :
    ∃ a b : Region, ∃ cost,
      s.fringe = (Pointer.Lazy.Skeleton.node a b).fringe ∧
      Rotations s.tree (.node a.tree b.tree) cost ∧
      (cost : ℝ) + auxiliaryPotential (.node a (.hole b.tree)) + auxiliaryPotential b - auxiliaryPotential s ≤
        3 * Real.logb 2 s.size + 1 := by
  obtain ⟨a, b, hl, hr, hf, rotations⟩ := auxiliary_split s k positive valid
  have bound := Splay.Updates.split_bound (shape s) k (by rw [shape_size]; exact valid)
  refine ⟨a, b, _, hf, rotations, ?_⟩
  simpa only [← hl, ← hr, Splay.Updates.unitPotential, auxiliaryPotential, shape_size] using bound

theorem auxiliary_join_bound (left right : Region)
    (attached : left.fringe.getLast? = some right.tree) :
    ∃ u cost, u.fringe = left.fringe.dropLast ++ right.fringe ∧
      Rotations left.tree u.tree cost ∧
      (cost : ℝ) + auxiliaryPotential u - auxiliaryPotential left - auxiliaryPotential right ≤
        3 * Real.logb 2 (left.size + right.size : Nat) + 1 := by
  obtain ⟨u, hu, hf, rotations⟩ := auxiliary_join left right attached
  have bound := Splay.Updates.join_bound (shape left) (shape right)
  refine ⟨u, _, hf, rotations, ?_⟩
  simpa only [← hu, Splay.Updates.unitPotential, auxiliaryPotential, shape_size] using bound

end RotationBST.Geometric.Region
