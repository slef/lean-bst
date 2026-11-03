module

public import RotationBST.Algorithms.Tango.State.Cut.Prefix

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Region Pointer.Lazy.Skeleton

/-- The executable suffix cut has the specified boundary and suffix size. -/
theorem cutSuffix_spec (s : MarkedTree) (first : Nat)
    (positive : 0 < first) (valid : first < s.region.size) :
    ∃ l r : MarkedTree, ∃ cl : Bool,
      (s.cutSuffix first).1 = .node l r cl true ∧
      (if cl then 0 else l.region.size) + 1 = first ∧
      r.region.size = s.region.size - first ∧
      s.fringe = (MarkedTree.node l r cl false).fringe ∧
      Rotations s.tree (s.cutSuffix first).1.tree (s.cutSuffix first).2 ∧
      ((s.cutSuffix first).2 : ℝ) + (s.cutSuffix first).1.potential - s.potential ≤
        3 * Real.logb 2 s.region.size + 1 := by
  obtain ⟨l, r, cl, cr, exposed, rank, hf, rotations, bound⟩ :=
    splayRoot_expose s (first - 1) (by omega)
  have sizes := region_size_eq hf
  cases cr
  · have result : s.cutSuffix first = (.node l r cl true, (s.splayRoot (first - 1)).2) := by
      simp only [cutSuffix, exposed]
    rw [result]
    refine ⟨l, r, cl, rfl, by omega, ?_, hf, rotations, ?_⟩
    · cases cl <;> simp only [region, size, ite_true, Bool.false_eq_true, ite_false] at sizes rank <;> omega
    · have decrease := mark_right l r cl
      dsimp only [Prod.fst, Prod.snd]
      linarith
  · cases cl <;> simp only [region, size, ite_true, Bool.false_eq_true, ite_false] at sizes rank <;> omega

end RotationBST.Tango.MarkedTree
