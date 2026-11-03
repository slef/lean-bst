module

public import RotationBST.Algorithms.Tango.State.Join.Defs
public import RotationBST.Algorithms.Tango.State.Splay.Proofs
public import RotationBST.Algorithms.Tango.State.Marking

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Arboral.Region Pointer.Lazy.Skeleton

/-- The executable maximum-splay join has the expected endpoint and cost. -/
theorem joinBack_spec (s right : MarkedTree) (positive : 0 < s.region.size)
    (attached : s.fringe.getLast? = some right) :
    ∃ l : MarkedTree, ∃ cl : Bool,
      s.joinBack.1 = .node l right cl false ∧
      s.fringe = (MarkedTree.node l right cl true).fringe ∧
      Rotations s.tree s.joinBack.1.tree s.joinBack.2 ∧
      (s.joinBack.2 : ℝ) + s.joinBack.1.potential - s.potential ≤
        3 * Real.logb 2 (s.region.size + right.region.size : Nat) + 1 := by
  obtain ⟨l, r, cl, cr, exposed, rank, hf, rotations, bound⟩ :=
    splayRoot_expose s (s.region.size - 1) (by omega)
  have sizes := region_size_eq hf
  have hz : (if cr then 0 else r.region.size) = 0 := by
    cases cl <;> cases cr <;>
      simp only [region, size, ite_true, Bool.false_eq_true, ite_false] at sizes rank ⊢ <;> omega
  have hright : r = right := by
    rw [hf] at attached
    cases cr
    · simp only [Bool.false_eq_true, ite_false] at hz
      cases r with
      | nil => simpa [fringe] using attached
      | node a b ca cb => simp [region, size] at hz
    · simpa [fringe] using attached
  subst r
  have root_size : (MarkedTree.node l right cl false).region.size = s.region.size + right.region.size := by
    cases cl <;> cases cr <;>
      simp only [region, size, ite_true, Bool.false_eq_true, ite_false] at sizes hz ⊢ <;> omega
  have result : s.joinBack = (.node l right cl false, (s.splayRoot (s.region.size - 1)).2) := by
    simp only [joinBack, exposed]
  rw [result]
  refine ⟨l, cl, rfl, ?_, rotations, ?_⟩
  · cases cr
    · simp only [Bool.false_eq_true, ite_false] at hz
      cases right with
      | nil => simpa [fringe] using hf
      | node a b ca cb => simp [region, size] at hz
    · exact hf
  · have logs := Splay.Updates.log_nat_mono
      (show s.region.size ≤ s.region.size + right.region.size by omega)
    rw [potential_node, ← sizes] at bound
    rw [potential_node, root_size]
    linarith

/-- The executable minimum-splay join has the expected endpoint and cost. -/
theorem joinFront_spec (s left : MarkedTree) (positive : 0 < s.region.size)
    (attached : s.fringe.head? = some left) :
    ∃ r : MarkedTree, ∃ cr : Bool,
      s.joinFront.1 = .node left r false cr ∧
      s.fringe = (MarkedTree.node left r true cr).fringe ∧
      Rotations s.tree s.joinFront.1.tree s.joinFront.2 ∧
      (s.joinFront.2 : ℝ) + s.joinFront.1.potential - s.potential ≤
        3 * Real.logb 2 (s.region.size + left.region.size : Nat) + 1 := by
  obtain ⟨l, r, cl, cr, exposed, rank, hf, rotations, bound⟩ := splayRoot_expose s 0 positive
  have sizes := region_size_eq hf
  have hleft : l = left := by
    rw [hf] at attached
    cases cl
    · simp only [Bool.false_eq_true, ite_false] at rank
      cases l with
      | nil => simpa [fringe] using attached
      | node a b ca cb => simp [region, size] at rank
    · simpa [fringe] using attached
  subst l
  have root_size : (MarkedTree.node left r false cr).region.size = s.region.size + left.region.size := by
    cases cl <;> cases cr <;>
      simp only [region, size, ite_true, Bool.false_eq_true, ite_false] at sizes rank ⊢ <;> omega
  have result : s.joinFront = (.node left r false cr, (s.splayRoot 0).2) := by
    simp only [joinFront, exposed]
  rw [result]
  refine ⟨r, cr, rfl, ?_, rotations, ?_⟩
  · cases cl
    · simp only [Bool.false_eq_true, ite_false] at rank
      cases left with
      | nil => simpa [fringe] using hf
      | node a b ca cb => simp [region, size] at rank
    · exact hf
  · have logs := Splay.Updates.log_nat_mono
      (show s.region.size ≤ s.region.size + left.region.size by omega)
    rw [potential_node, ← sizes] at bound
    rw [potential_node, root_size]
    linarith

end RotationBST.Tango.MarkedTree
