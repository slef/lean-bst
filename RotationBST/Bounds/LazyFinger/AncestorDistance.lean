module

public import RotationBST.Bounds.LazyFinger.Ancestors
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

theorem common_ancestors_card (t : Tree) (lo x y : Nat)
    (hx : lo ≤ x ∧ x < lo + t.size) (hy : lo ≤ y ∧ y < lo + t.size) :
    ((t.searchPath lo x).toFinset ∩ (t.searchPath lo y).toFinset).card =
      lcaDepth t (x - lo) (y - lo) + 1 := by
  induction t generalizing lo with
  | nil => simp [Tree.size] at hx; omega
  | node l r ihl ihr =>
    by_cases hl : x < lo + l.size ∧ y < lo + l.size
    · have hx' : x - lo < l.size := by omega
      have hy' : y - lo < l.size := by omega
      simp only [Tree.searchPath, hl.1, hl.2, ↓reduceIte, List.toFinset_cons,
        ← Finset.insert_inter_distrib]
      have hn : lo + l.size ∉ (l.searchPath lo x).toFinset ∩ (l.searchPath lo y).toFinset := by
        intro h
        have hb := l.searchPath_bounds lo x _ (List.mem_toFinset.mp (Finset.mem_inter.mp h).1)
        omega
      rw [Finset.card_insert_of_notMem hn, ihl lo ⟨hx.1, hl.1⟩ ⟨hy.1, hl.2⟩]
      simp [lcaDepth, hx', hy']
    · by_cases hr : lo + l.size < x ∧ lo + l.size < y
      · have hx' : ¬ x < lo + l.size := by omega
        have hy' : ¬ y < lo + l.size := by omega
        have hxe : x ≠ lo + l.size := by omega
        have hye : y ≠ lo + l.size := by omega
        have hxr : lo + l.size + 1 ≤ x ∧ x < lo + l.size + 1 + r.size := by
          simp only [Tree.size] at hx; omega
        have hyr : lo + l.size + 1 ≤ y ∧ y < lo + l.size + 1 + r.size := by
          simp only [Tree.size] at hy; omega
        simp only [Tree.searchPath, hx', hy', hxe, hye, ↓reduceIte, List.toFinset_cons,
          ← Finset.insert_inter_distrib]
        have hn : lo + l.size ∉ (r.searchPath (lo + l.size + 1) x).toFinset ∩
            (r.searchPath (lo + l.size + 1) y).toFinset := by
          intro h
          have hb := r.searchPath_bounds (lo + l.size + 1) x _
            (List.mem_toFinset.mp (Finset.mem_inter.mp h).1)
          omega
        rw [Finset.card_insert_of_notMem hn, ihr _ hxr hyr]
        have ex : x - (lo + l.size + 1) = x - lo - l.size - 1 := by omega
        have ey : y - (lo + l.size + 1) = y - lo - l.size - 1 := by omega
        have hxl : ¬ x - lo < l.size := by omega
        have hyl : ¬ y - lo < l.size := by omega
        have hxx : l.size < x - lo := by omega
        have hyy : l.size < y - lo := by omega
        simp [lcaDepth, hxl, hyl, hxx, hyy, ex, ey]
      · have he : (Tree.searchPath (.node l r) lo x).toFinset ∩
            (Tree.searchPath (.node l r) lo y).toFinset = {lo + l.size} := by
          ext a
          simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_singleton]
          constructor
          · rintro ⟨hax, hay⟩
            by_contra hn
            have hsx := Tree.searchPath_mem_side l r lo x a hax hn
            have hsy := Tree.searchPath_mem_side l r lo y a hay hn
            omega
          · rintro rfl
            exact ⟨Tree.root_mem_searchPath l r lo x, Tree.root_mem_searchPath l r lo y⟩
        rw [he, Finset.card_singleton]
        have hl' : ¬ (x - lo < l.size ∧ y - lo < l.size) := by omega
        have hr' : ¬ (l.size < x - lo ∧ l.size < y - lo) := by omega
        simp [lcaDepth, hl', hr']

private theorem sum_indicator_eq_card (u s : Finset Nat) (sub : s ⊆ u) :
    (∑ a ∈ u, if a ∈ s then (1 : ℝ) else 0) = (s.card : ℝ) := by
  rw [← Finset.sum_filter]
  have he : u.filter (fun a => a ∈ s) = s := by
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨sub h, h⟩⟩
  simp [he]

/-- Distance counts ancestors of exactly one endpoint. The arithmetic indicator
form is convenient for finite expectations and includes neither a double-counted
root nor a spurious charge for repeated requests. -/
theorem distance_ancestor_sum (t : Tree) (lo x y : Nat)
    (hx : lo ≤ x ∧ x < lo + t.size) (hy : lo ≤ y ∧ y < lo + t.size) :
    (distance t (x - lo) (y - lo) : ℝ) =
      ∑ a ∈ Finset.Ico lo (lo + t.size),
        ((if a ∈ t.searchPath lo x then (1 : ℝ) else 0) +
         (if a ∈ t.searchPath lo y then (1 : ℝ) else 0) -
         2 * (if a ∈ t.searchPath lo x ∧ a ∈ t.searchPath lo y then (1 : ℝ) else 0)) := by
  have sub (z : Nat) : (t.searchPath lo z).toFinset ⊆ Finset.Ico lo (lo + t.size) := by
    intro a ha
    exact Finset.mem_Ico.mpr (t.searchPath_bounds lo z a (List.mem_toFinset.mp ha))
  have hX := sum_indicator_eq_card _ _ (sub x)
  have hY := sum_indicator_eq_card _ _ (sub y)
  have hXY := sum_indicator_eq_card (Finset.Ico lo (lo + t.size))
    ((t.searchPath lo x).toFinset ∩ (t.searchPath lo y).toFinset)
    (fun a ha => sub x (Finset.mem_inter.mp ha).1)
  simp only [Finset.mem_inter, List.mem_toFinset] at hX hY hXY
  rw [List.toFinset_card_of_nodup (t.searchPath_nodup lo x), searchPath_length t lo x hx] at hX
  rw [List.toFinset_card_of_nodup (t.searchPath_nodup lo y), searchPath_length t lo y hy] at hY
  rw [common_ancestors_card t lo x y hx hy] at hXY
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hX, hY, hXY]
  have h := distance_add_twice_lca t (x - lo) (y - lo)
  have hh : (distance t (x - lo) (y - lo) : ℝ) + 2 * lcaDepth t (x - lo) (y - lo) =
      (Tree.depth t (x - lo) : ℝ) + Tree.depth t (y - lo) := by exact_mod_cast h
  push_cast
  linarith

end RotationBST.LazyFinger
