module

public import RotationBST.Algorithms.Tango.State.Cut.Suffix

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Geometric.Region Pointer.Lazy.Skeleton

/-- Both boundary splays of the executable interior cut are charged, including
the potential change of the whole marked tree. -/
theorem cutInterior_spec (s : MarkedTree) (first pastLast : Nat)
    (positive : 0 < first) (ordered : first < pastLast) (interior : pastLast < s.region.size) :
    ∃ a middle c : MarkedTree, ∃ ca cc : Bool,
      (s.cutInterior first pastLast).1 = .node a (.node middle c true cc) ca false ∧
      (if ca then 0 else a.region.size) + 1 = first ∧ middle.region.size = pastLast - first ∧
      s.fringe = (MarkedTree.node a (.node middle c false cc) ca false).fringe ∧
      Rotations s.tree (s.cutInterior first pastLast).1.tree (s.cutInterior first pastLast).2 ∧
      ((s.cutInterior first pastLast).2 : ℝ) + (s.cutInterior first pastLast).1.potential - s.potential ≤
        6 * Real.logb 2 s.region.size + 2 := by
  obtain ⟨a, b, ca, cb, exposed, rank, hf, ra, ba⟩ :=
    splayRoot_expose s (first - 1) (by omega)
  have sizes := region_size_eq hf
  cases cb
  · have bs : b.region.size = s.region.size - first := by
      cases ca <;> simp only [region, size, ite_true, Bool.false_eq_true, ite_false] at sizes rank <;> omega
    obtain ⟨middle, c, cc, cut, hm, hg, rb, bb⟩ :=
      cutPrefix_spec b (pastLast - first) (by omega) (by omega)
    have result : s.cutInterior first pastLast =
        (.node a (.node middle c true cc) ca false,
          (s.splayRoot (first - 1)).2 + (b.cutPrefix (pastLast - first)).2) := by
      simp only [cutInterior, exposed, cut]
    rw [result]
    rw [cut] at rb bb
    refine ⟨a, middle, c, ca, cc, rfl, by omega, hm, ?_, ra.append rb.inRight, ?_⟩
    · simpa only [fringe, Bool.false_eq_true, ite_false, hg] using hf
    · have bsize := region_size_eq hg
      have smaller : (MarkedTree.node middle c true cc).region.size ≤ b.region.size := by
        rw [bsize]
        cases cc <;> simp [region, size]
      have transfer := replace_right_le a b (.node middle c true cc) ca false smaller
      have logs := Splay.Updates.log_nat_mono (show b.region.size ≤ s.region.size by omega)
      simp only [Nat.cast_add]
      linarith
  · cases ca <;> simp only [region, size, ite_true, Bool.false_eq_true, ite_false] at sizes rank <;> omega

end RotationBST.Tango.MarkedTree
