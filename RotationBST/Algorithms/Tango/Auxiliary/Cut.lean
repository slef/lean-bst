module

public import RotationBST.Algorithms.Tango.Auxiliary.Analysis

@[expose] public section
namespace RotationBST.Region
open Pointer.Lazy.Skeleton

/-- Expose an auxiliary rank, counting only active nodes, with the actual
rotation cost in the containing BST. -/
theorem expose_rank (s : Region) (k : Nat) (valid : k < s.size) :
    ∃ a b : Region, ∃ cost,
      a.size = k ∧ a.size + b.size + 1 = s.size ∧
      s.fringe = (Pointer.Lazy.Skeleton.node a b).fringe ∧
      Rotations s.tree (.node a.tree b.tree) cost ∧
      (cost : ℝ) + auxiliaryPotential (.node a b) - auxiliaryPotential s ≤
        3 * Real.logb 2 s.size + 1 := by
  have access := (Splay.run_correct (shape s) k (by rwa [shape_size])).1
  have bound := Splay.Updates.unit_access (shape s) k (by rwa [shape_size])
  obtain ⟨u, hu, hf, rotations⟩ := lift_rotations access.1 s rfl
  have sizes := access.1.size_eq
  cases u with
  | hole t => rw [← hu] at access; exact False.elim access.2
  | node a b =>
    refine ⟨a, b, _, ?_, ?_, hf, rotations, ?_⟩
    · simpa only [← hu, shape, shape_size] using access.2
    · simpa only [← hu, shape, Tree.size, shape_size, Nat.add_right_comm] using sizes.symm
    · simpa only [← hu, Splay.Updates.unitPotential, auxiliaryPotential, shape_size] using bound

theorem auxiliaryPotential_node (a b : Region) :
    auxiliaryPotential (.node a b) = auxiliaryPotential a + auxiliaryPotential b +
      Real.logb 2 (a.size + b.size + 1 : Nat) := by
  simpa only [Splay.Updates.unitPotential, auxiliaryPotential, shape, Tree.size, shape_size, Nat.add_right_comm] using
    Splay.Updates.unitPotential_node (shape a) (shape b)

theorem auxiliaryPotential_hole (t : Tree) : auxiliaryPotential (.hole t) = 0 := rfl

/-- Cut out an interior interval of auxiliary ranks `[i,j)`. Two boundary
splays expose it as a subtree, which can then be marked as a separate component.
The cost is independent of the sizes of all attached fringe subtrees. -/
theorem auxiliary_cut_interior (s : Region) (i j : Nat)
    (positive : 0 < i) (ordered : i ≤ j) (interior : j < s.size) :
    ∃ a middle c : Region, ∃ cost,
      a.size + 1 = i ∧ middle.size = j - i ∧
      a.size + middle.size + c.size + 2 = s.size ∧
      s.fringe = (Pointer.Lazy.Skeleton.node a (.node middle c)).fringe ∧
      Rotations s.tree (.node a.tree (.node middle.tree c.tree)) cost ∧
      (cost : ℝ) + auxiliaryPotential (.node a (.node (.hole middle.tree) c)) +
        auxiliaryPotential middle - auxiliaryPotential s ≤ 6 * Real.logb 2 s.size + 2 := by
  obtain ⟨a, b, ca, ha, hab, hf, ra, ba⟩ := expose_rank s (i - 1) (by omega)
  obtain ⟨middle, c, cb, hm, hmc, hg, rb, bb⟩ := expose_rank b (j - i) (by omega)
  refine ⟨a, middle, c, ca + cb, by omega, hm, by omega, ?_, ra.append rb.inRight, ?_⟩
  · simpa only [fringe, hg] using hf
  · have logs := Splay.Updates.log_nat_mono (show b.size ≤ s.size by omega)
    have inner := Splay.Updates.log_nat_mono
      (show 0 + c.size + 1 ≤ middle.size + c.size + 1 by omega)
    have outer := Splay.Updates.log_nat_mono
      (show a.size + (0 + c.size + 1) + 1 ≤ s.size by omega)
    have total' : a.size + b.size + 1 = s.size := hab
    simp only [auxiliaryPotential_node, auxiliaryPotential_hole, size] at ba bb ⊢
    rw [total'] at ba
    simp only [Nat.cast_add, Nat.cast_one, zero_add, add_assoc, add_comm, add_left_comm] at *
    linarith

/-- A prefix interval needs just its successor boundary. -/
theorem auxiliary_cut_prefix (s : Region) (j : Nat) (valid : j < s.size) :
    ∃ middle c : Region, ∃ cost,
      middle.size = j ∧ middle.size + c.size + 1 = s.size ∧
      s.fringe = (Pointer.Lazy.Skeleton.node middle c).fringe ∧
      Rotations s.tree (.node middle.tree c.tree) cost ∧
      (cost : ℝ) + auxiliaryPotential (.node (.hole middle.tree) c) +
        auxiliaryPotential middle - auxiliaryPotential s ≤ 3 * Real.logb 2 s.size + 1 := by
  obtain ⟨middle, c, cost, hm, hs, hf, rotations, bound⟩ := expose_rank s j valid
  refine ⟨middle, c, cost, hm, hs, hf, rotations, ?_⟩
  have logs := Splay.Updates.log_nat_mono (show 0 + c.size + 1 ≤ s.size by omega)
  simp only [auxiliaryPotential_node, auxiliaryPotential_hole, size] at bound ⊢
  rw [hs] at bound
  linarith

/-- A suffix interval needs just its predecessor boundary. -/
theorem auxiliary_cut_suffix (s : Region) (i : Nat) (positive : 0 < i) (valid : i ≤ s.size) :
    ∃ a middle : Region, ∃ cost,
      a.size + 1 = i ∧ a.size + middle.size + 1 = s.size ∧
      s.fringe = (Pointer.Lazy.Skeleton.node a middle).fringe ∧
      Rotations s.tree (.node a.tree middle.tree) cost ∧
      (cost : ℝ) + auxiliaryPotential (.node a (.hole middle.tree)) +
        auxiliaryPotential middle - auxiliaryPotential s ≤ 3 * Real.logb 2 s.size + 1 := by
  obtain ⟨a, middle, cost, ha, hs, hf, rotations, bound⟩ := expose_rank s (i - 1) (by omega)
  refine ⟨a, middle, cost, by omega, hs, hf, rotations, ?_⟩
  have logs := Splay.Updates.log_nat_mono (show a.size + 0 + 1 ≤ s.size by omega)
  simp only [auxiliaryPotential_node, auxiliaryPotential_hole, size] at bound ⊢
  rw [hs] at bound
  linarith

end RotationBST.Region
