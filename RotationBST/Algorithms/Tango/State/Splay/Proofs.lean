module

public import RotationBST.Algorithms.Tango.State.Splay.Defs
public import RotationBST.Algorithms.Tango.State.Rebuild.Proofs
public import RotationBST.Algorithms.Tango.Auxiliary.Execution

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Region

/-- The executable splay preserves the entire marked fringe, serves its active
rank, and has the logarithmic amortized bound against whole-tree potential. -/
theorem splayRoot_spec (s : MarkedTree) (rank : Nat) (valid : rank < s.region.size) :
    s.fringe = (s.splayRoot rank).1.fringe ∧
      Access (shape s.region) (shape (s.splayRoot rank).1.region) rank (s.splayRoot rank).2 ∧
      Rotations s.tree (s.splayRoot rank).1.tree (s.splayRoot rank).2 ∧
      ((s.splayRoot rank).2 : ℝ) + (s.splayRoot rank).1.potential - s.potential ≤
        3 * Real.logb 2 s.region.size + 1 := by
  have access := (Splay.run_correct (shape s.region) rank (by rwa [shape_size])).1
  have bound := Splay.Updates.unit_access (shape s.region) rank (by rwa [shape_size])
  obtain ⟨target, fringe, rotations⟩ := rebuild_rotations s _ _ access.1
  have hf : s.fringe = (s.splayRoot rank).1.fringe := fringe
  have ht : shape (s.splayRoot rank).1.region = (Splay.run (shape s.region) rank).1 := target
  have cost : (s.splayRoot rank).2 = (Splay.run (shape s.region) rank).2 := rfl
  refine ⟨hf, ?_, rotations, ?_⟩
  · simpa only [ht, cost] using access
  · have difference := potential_difference hf
    have localBound : ((s.splayRoot rank).2 : ℝ) + auxiliaryPotential (s.splayRoot rank).1.region -
        auxiliaryPotential s.region ≤ 3 * Real.logb 2 s.region.size + 1 := by
      simpa only [Splay.Updates.unitPotential, auxiliaryPotential, ht, cost, shape_size] using bound
    linarith

/-- Expose the concrete node returned by a valid component splay. -/
theorem splayRoot_expose (s : MarkedTree) (rank : Nat) (valid : rank < s.region.size) :
    ∃ l r : MarkedTree, ∃ cl cr : Bool,
      (s.splayRoot rank).1 = .node l r cl cr ∧
      (if cl then 0 else l.region.size) = rank ∧
      s.fringe = (MarkedTree.node l r cl cr).fringe ∧
      Rotations s.tree (.node l.tree r.tree) (s.splayRoot rank).2 ∧
      ((s.splayRoot rank).2 : ℝ) + (MarkedTree.node l r cl cr).potential - s.potential ≤
        3 * Real.logb 2 s.region.size + 1 := by
  obtain ⟨hf, access, rotations, bound⟩ := splayRoot_spec s rank valid
  generalize hu : (s.splayRoot rank).1 = u at hf access rotations bound
  cases u with
  | nil => exact False.elim access.2
  | node l r cl cr =>
    refine ⟨l, r, cl, cr, rfl, ?_, hf, rotations, bound⟩
    have root := access.2
    cases cl <;> cases cr <;> simpa only [region, shape, ite_true, Bool.false_eq_true,
      ite_false, Tree.size, shape_size] using root

end RotationBST.Tango.MarkedTree
