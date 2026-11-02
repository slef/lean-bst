module

public import RotationBST.Tango.Auxiliary.Cut

@[expose] public section
namespace RotationBST.Arboral.Region
open Pointer.Lazy.Skeleton

/-- Merge a component attached at an interior fringe position. Two splays in
its parent expose the bounding keys; removing the intervening mark then joins
both components without an additional rotation. -/
theorem auxiliary_join_interior (s middle : Region) (i : Nat)
    (positive : 0 < i) (interior : i < s.size)
    (attached : s.fringe[i]? = some middle.tree) :
    ∃ a c : Region, ∃ cost,
      a.size + 1 = i ∧ a.size + c.size + 2 = s.size ∧
      s.fringe = (Pointer.Lazy.Skeleton.node a (.node (.hole middle.tree) c)).fringe ∧
      Rotations s.tree (.node a.tree (.node middle.tree c.tree)) cost ∧
      (cost : ℝ) + auxiliaryPotential (.node a (.node middle c)) -
        auxiliaryPotential s - auxiliaryPotential middle ≤
          8 * Real.logb 2 (s.size + middle.size : Nat) + 2 := by
  obtain ⟨a, b, ca, ha, hab, hf, ra, ba⟩ := expose_rank s (i - 1) (by omega)
  obtain ⟨left, c, cb, hl, hlc, hg, rb, bb⟩ := expose_rank b 0 (by omega)
  cases left with
  | node l r => simp only [size] at hl; omega
  | hole t =>
    have hf0 : b.fringe[0]? = some middle.tree := by
      rw [hf, fringe, List.getElem?_append_right (by rw [fringe_length]; omega)] at attached
      have hi : i - a.fringe.length = 0 := by rw [fringe_length]; omega
      simpa only [hi] using attached
    have ht : t = middle.tree := by
      rw [hg] at hf0
      simpa only [fringe, List.singleton_append, List.getElem?_cons_zero, Option.some.injEq] using hf0
    subst t
    refine ⟨a, c, ca + cb, by omega, ?_, ?_, ra.append rb.inRight, ?_⟩
    · simp only [size] at hlc; omega
    · simpa only [fringe, hg] using hf
    · have s_le : s.size ≤ s.size + middle.size := by omega
      have logs := Splay.Updates.log_nat_mono s_le
      have logb := Splay.Updates.log_nat_mono (show b.size ≤ s.size + middle.size by omega)
      have loginner := Splay.Updates.log_nat_mono
        (show middle.size + c.size + 1 ≤ s.size + middle.size by simp only [size] at hlc; omega)
      have logouter := Splay.Updates.log_nat_mono
        (show a.size + (middle.size + 1 + c.size) + 1 ≤ s.size + middle.size by
          simp only [size] at hlc; omega)
      have ns := Bounds.logb_nat_nonneg s.size
      have nb := Bounds.logb_nat_nonneg (0 + c.size + 1)
      simp only [auxiliaryPotential_node, auxiliaryPotential_hole, size] at ba bb ⊢
      rw [hab] at ba
      simp only [Nat.cast_add, Nat.cast_one, zero_add, add_assoc, add_comm, add_left_comm] at *
      linarith

/-- Joining at the first fringe subtree uses one minimum splay. -/
theorem auxiliary_join_front (s middle : Region) (nonempty : 0 < s.size)
    (attached : s.fringe.head? = some middle.tree) :
    ∃ c : Region, ∃ cost,
      c.size + 1 = s.size ∧ s.fringe = (Pointer.Lazy.Skeleton.node (.hole middle.tree) c).fringe ∧
      Rotations s.tree (.node middle.tree c.tree) cost ∧
      (cost : ℝ) + auxiliaryPotential (.node middle c) - auxiliaryPotential s - auxiliaryPotential middle ≤
        3 * Real.logb 2 (s.size + middle.size : Nat) + 1 := by
  obtain ⟨left, c, cost, hl, hs, hf, rotations, bound⟩ := expose_rank s 0 nonempty
  cases left with
  | node l r => simp only [size] at hl; omega
  | hole t =>
    have ht : t = middle.tree := by
      rw [hf] at attached
      simpa only [fringe, List.singleton_append, List.head?_cons, Option.some.injEq] using attached
    subst t
    refine ⟨c, cost, by simpa only [size, zero_add] using hs, hf, rotations, ?_⟩
    have logs := Splay.Updates.log_nat_mono (show s.size ≤ s.size + middle.size by omega)
    have total : middle.size + c.size + 1 = s.size + middle.size := by simp only [size] at hs; omega
    simp only [auxiliaryPotential_node, auxiliaryPotential_hole, size] at bound ⊢
    rw [total]
    simp only [size] at hs
    rw [hs] at bound
    linarith

end RotationBST.Arboral.Region
