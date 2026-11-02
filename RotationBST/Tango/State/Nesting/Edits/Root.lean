module

public import RotationBST.Tango.State.Nesting.Edits.Simulation

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Pointer.Lazy.Skeleton

/-- Detach the preferred left component at a reference root. -/
theorem detach_left (s l r : MarkedTree) (same : s.nesting = (MarkedTree.node l r false true).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (MarkedTree.node l r true true).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 6 * Real.logb 2 (l.region.size + 1 : Nat) + 2 := by
  cases hl : l with
  | nil =>
    refine ⟨s, 0, ?_, .refl, ?_⟩
    · simpa only [hl, nesting, ComponentNesting.fringe, ite_true, Bool.false_eq_true, ite_false] using same
    · simp [region, size]
  | node a b ca cb =>
    have positive : 0 < l.region.size := by rw [hl]; simp [region, size]
    have total : (MarkedTree.node l r false true).region.size = l.region.size + 1 := by simp [region, size]
    obtain ⟨t, cost, hn, rotations, bound⟩ := simulate_cut s (.node l r false true) same 0 l.region.size
      positive (by rw [total]; omega) (by rw [total]; omega)
    have grouped := mark_left_nesting l r true (by rw [hl]; simp)
    refine ⟨t, cost, ?_, rotations, ?_⟩
    · rw [Nat.sub_zero, ← grouped] at hn
      simpa only [hl] using hn
    · rw [total] at bound
      simpa only [hl] using bound

/-- Detach the preferred right component at a reference root. -/
theorem detach_right (s l r : MarkedTree) (same : s.nesting = (MarkedTree.node l r true false).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (MarkedTree.node l r true true).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 6 * Real.logb 2 (r.region.size + 1 : Nat) + 2 := by
  cases hr : r with
  | nil =>
    refine ⟨s, 0, ?_, .refl, ?_⟩
    · simpa only [hr, nesting, ComponentNesting.fringe, ite_true, Bool.false_eq_true, ite_false] using same
    · simp [region, size]
  | node a b ca cb =>
    have positive : 0 < r.region.size := by rw [hr]; simp [region, size]
    have total : (MarkedTree.node l r true false).region.size = r.region.size + 1 := by simp [region, size]; omega
    obtain ⟨t, cost, hn, rotations, bound⟩ := simulate_cut s (.node l r true false) same 1 (r.region.size + 1)
      (by omega) (by rw [total]) (by rw [total]; omega)
    have grouped := mark_right_nesting l r true (by rw [hr]; simp)
    simp only [ite_true, Nat.zero_add] at grouped
    refine ⟨t, cost, ?_, rotations, ?_⟩
    · rw [Nat.add_sub_cancel, ← grouped] at hn
      simpa only [hr] using hn
    · rw [total] at bound
      simpa only [hr] using bound

theorem attach_left (s l r : MarkedTree) (same : s.nesting = (MarkedTree.node l r true true).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (MarkedTree.node l r false true).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 8 * Real.logb 2 (l.region.size + 1 : Nat) + 2 := by
  obtain ⟨t, cost, hn, rotations, bound⟩ := simulate_merge s (.node l r true true) l same 0
    (by simp [region, size]) (by simp [region, size]) (by rfl)
  refine ⟨t, cost, hn.trans (unmark_left_nesting l r true).symm, rotations, ?_⟩
  simpa only [region, size, ite_true, Nat.zero_add, Nat.add_zero, Nat.add_comm 1] using bound

theorem attach_right (s l r : MarkedTree) (same : s.nesting = (MarkedTree.node l r true true).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (MarkedTree.node l r true false).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 8 * Real.logb 2 (r.region.size + 1 : Nat) + 2 := by
  obtain ⟨t, cost, hn, rotations, bound⟩ := simulate_merge s (.node l r true true) r same 1
    (by simp [region, size]) (by simp [region, size]) (by rfl)
  refine ⟨t, cost, ?_, rotations, ?_⟩
  · simpa only [ite_true, Nat.zero_add] using hn.trans (unmark_right_nesting l r true).symm
  · simpa only [region, size, ite_true, Nat.zero_add, Nat.add_zero, Nat.add_comm 1] using bound

/-- One left-to-right preference switch uses a cut followed by a join, in the
actual BST, with the updated component nesting and global amortized bound. -/
theorem switch_right (s l r : MarkedTree) (same : s.nesting = (MarkedTree.node l r false true).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (MarkedTree.node l r true false).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        14 * Real.logb 2 (l.region.size + r.region.size + 1 : Nat) + 4 := by
  obtain ⟨u, a, hu, ra, ba⟩ := detach_left s l r same
  obtain ⟨t, b, ht, rb, bb⟩ := attach_right u l r hu
  refine ⟨t, a + b, ht, ra.append rb, ?_⟩
  have left := Splay.Updates.log_nat_mono (show l.region.size + 1 ≤ l.region.size + r.region.size + 1 by omega)
  have right := Splay.Updates.log_nat_mono (show r.region.size + 1 ≤ l.region.size + r.region.size + 1 by omega)
  simp only [Nat.cast_add] at *
  linarith

theorem switch_left (s l r : MarkedTree) (same : s.nesting = (MarkedTree.node l r true false).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (MarkedTree.node l r false true).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        14 * Real.logb 2 (l.region.size + r.region.size + 1 : Nat) + 4 := by
  obtain ⟨u, a, hu, ra, ba⟩ := detach_right s l r same
  obtain ⟨t, b, ht, rb, bb⟩ := attach_left u l r hu
  refine ⟨t, a + b, ht, ra.append rb, ?_⟩
  have left := Splay.Updates.log_nat_mono (show l.region.size + 1 ≤ l.region.size + r.region.size + 1 by omega)
  have right := Splay.Updates.log_nat_mono (show r.region.size + 1 ≤ l.region.size + r.region.size + 1 by omega)
  simp only [Nat.cast_add] at *
  linarith

end RotationBST.Tango.MarkedTree
