module

public import RotationBST.Algorithms.Tango.State.Cut.Defs
public import RotationBST.Algorithms.Tango.State.Splay.Proofs
public import RotationBST.Algorithms.Tango.State.Marking

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Arboral.Region Pointer.Lazy.Skeleton

/-- The executable prefix cut returns the specified boundary mark, realizes its
rotation count, and satisfies the same global-potential bound as the splay. -/
theorem cutPrefix_spec (s : MarkedTree) (count : Nat)
    (positive : 0 < count) (valid : count < s.region.size) :
    ∃ l r : MarkedTree, ∃ cr : Bool,
      (s.cutPrefix count).1 = .node l r true cr ∧ l.region.size = count ∧
      s.fringe = (MarkedTree.node l r false cr).fringe ∧
      Rotations s.tree (s.cutPrefix count).1.tree (s.cutPrefix count).2 ∧
      ((s.cutPrefix count).2 : ℝ) + (s.cutPrefix count).1.potential - s.potential ≤
        3 * Real.logb 2 s.region.size + 1 := by
  obtain ⟨hf, access, rotations, bound⟩ := splayRoot_spec s count valid
  generalize hu : (s.splayRoot count).1 = u at hf access rotations bound
  cases u with
  | nil => exact False.elim access.2
  | node l r cl cr =>
    have root := access.2
    cases cl
    · have rank : l.region.size = count := by
        cases cr <;> simpa only [region, shape, ite_true, Bool.false_eq_true, ite_false, Tree.size, shape_size] using root
      have result : s.cutPrefix count = (.node l r true cr, (s.splayRoot count).2) := by
        simp only [cutPrefix, hu]
      rw [result]
      refine ⟨l, r, cr, rfl, rank, hf, rotations, ?_⟩
      have decrease := mark_left l r cr
      dsimp only [Prod.fst, Prod.snd]
      linarith
    · cases cr <;> simp only [region, shape, ite_true, Bool.false_eq_true, ite_false, Tree.size] at root <;> omega

end RotationBST.Tango.MarkedTree
