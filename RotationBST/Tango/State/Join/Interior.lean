module

public import RotationBST.Tango.State.Join.Ends

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Arboral.Region Pointer.Lazy.Skeleton

/-- The executable interior join charges both boundary splays and the change
in potential of the enclosing component. -/
theorem joinInterior_spec (s middle : MarkedTree) (i : Nat)
    (positive : 0 < i) (interior : i < s.region.size)
    (attached : s.fringe[i]? = some middle) :
    ∃ a c : MarkedTree, ∃ ca cc : Bool,
      (s.joinInterior i).1 = .node a (.node middle c false cc) ca false ∧
      (if ca then 0 else a.region.size) + 1 = i ∧
      s.fringe = (MarkedTree.node a (.node middle c true cc) ca false).fringe ∧
      Rotations s.tree (s.joinInterior i).1.tree (s.joinInterior i).2 ∧
      ((s.joinInterior i).2 : ℝ) + (s.joinInterior i).1.potential - s.potential ≤
        8 * Real.logb 2 (s.region.size + middle.region.size : Nat) + 2 := by
  obtain ⟨a, b, ca, cb, exposed, rank, hf, ra, ba⟩ := splayRoot_expose s (i - 1) (by omega)
  have sizes := region_size_eq hf
  cases cb
  · have bs : b.region.size = s.region.size - i := by
      cases ca <;> simp only [region, size, ite_true, Bool.false_eq_true, ite_false] at sizes rank <;> omega
    have leftlen : (if ca then [a] else a.fringe).length = i := by
      cases ca <;> simp only [ite_true, Bool.false_eq_true, ite_false, List.length_singleton,
        marked_fringe_length] at rank ⊢ <;> omega
    have hb : b.fringe.head? = some middle := by
      rw [hf] at attached
      change (((if ca then [a] else a.fringe) ++ b.fringe)[i]?) = some middle at attached
      rw [List.getElem?_append_right (by omega), leftlen, Nat.sub_self] at attached
      simpa only [List.head?_eq_getElem?] using attached
    obtain ⟨c, cc, joined, hg, rb, bb⟩ := joinFront_spec b middle (by omega) hb
    have result : s.joinInterior i =
        (.node a (.node middle c false cc) ca false, (s.splayRoot (i - 1)).2 + b.joinFront.2) := by
      simp only [joinInterior, exposed, joined]
    rw [result]
    rw [joined] at rb bb
    refine ⟨a, c, ca, cc, rfl, by omega, ?_, ra.append rb.inRight, ?_⟩
    · simpa only [fringe, Bool.false_eq_true, ite_false, hg] using hf
    · have bsize := region_size_eq hg
      have total : (MarkedTree.node a (.node middle c false cc) ca false).region.size =
          s.region.size + middle.region.size := by
        cases ca <;> cases cc <;>
          simp only [region, size, ite_true, Bool.false_eq_true, ite_false] at sizes bsize ⊢ <;> omega
      have logs := Splay.Updates.log_nat_mono
        (show s.region.size ≤ s.region.size + middle.region.size by omega)
      have logb := Splay.Updates.log_nat_mono
        (show b.region.size + middle.region.size ≤ s.region.size + middle.region.size by omega)
      have nonneg := Bounds.logb_nat_nonneg (s.region.size + middle.region.size)
      rw [potential_node, ← sizes] at ba
      rw [potential_node, total]
      simp only [Nat.cast_add] at *
      linarith
  · cases ca <;> simp only [region, size, ite_true, Bool.false_eq_true, ite_false] at sizes rank <;> omega

end RotationBST.Tango.MarkedTree
