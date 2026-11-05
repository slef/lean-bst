module

public import RotationBST.Bounds.LazyFinger.Edges.Definitions.Abstract
public import RotationBST.Bounds.LazyFinger.Proofs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

theorem cut_symm (lo hi x y : Nat) : cut lo hi x y = cut lo hi y x := by
  simp only [cut, iff_comm]

theorem edgeMovement_node (l r : Tree) (lo x y : Nat) :
    edgeMovement (.node l r) lo x y = cut lo (lo + (.node l r : Tree).size) x y +
      edgeMovement l lo x y + edgeMovement r (lo + l.size + 1) x y := rfl

theorem edgeMovement_symm (t : Tree) (lo x y : Nat) :
    edgeMovement t lo x y = edgeMovement t lo y x := by
  induction t generalizing lo with
  | nil => rfl
  | node l r ihl ihr => simp only [edgeMovement_node, cut_symm lo _ x y, ihl, ihr]

theorem edgeMovement_outside (t : Tree) (lo x y : Nat)
    (hx : ¬ (lo ≤ x ∧ x < lo + t.size))
    (hy : ¬ (lo ≤ y ∧ y < lo + t.size)) : edgeMovement t lo x y = 0 := by
  induction t generalizing lo with
  | nil => rfl
  | node l r ihl ihr =>
    have hxl : ¬ (lo ≤ x ∧ x < lo + l.size) := by simp only [Tree.size] at hx; omega
    have hyl : ¬ (lo ≤ y ∧ y < lo + l.size) := by simp only [Tree.size] at hy; omega
    have hxr : ¬ (lo + l.size + 1 ≤ x ∧ x < lo + l.size + 1 + r.size) := by
      simp only [Tree.size] at hx; omega
    have hyr : ¬ (lo + l.size + 1 ≤ y ∧ y < lo + l.size + 1 + r.size) := by
      simp only [Tree.size] at hy; omega
    simp [edgeMovement_node, cut, hx, hy, ihl lo hxl hyl, ihr _ hxr hyr]

/-- An entering or leaving transition follows the endpoint's root path and
crosses the subtree's incoming edge once. -/
theorem edgeMovement_enter (t : Tree) (lo x y : Nat)
    (hx : lo ≤ x ∧ x < lo + t.size)
    (hy : ¬ (lo ≤ y ∧ y < lo + t.size)) :
    edgeMovement t lo x y = Tree.depth t (x - lo) + 1 := by
  induction t generalizing lo with
  | nil => simp [Tree.size] at hx; omega
  | node l r ihl ihr =>
    have hyl : ¬ (lo ≤ y ∧ y < lo + l.size) := by simp only [Tree.size] at hy; omega
    have hyr : ¬ (lo + l.size + 1 ≤ y ∧ y < lo + l.size + 1 + r.size) := by
      simp only [Tree.size] at hy; omega
    rw [edgeMovement_node]
    simp only [cut, hx, hy, iff_false]
    rcases lt_trichotomy x (lo + l.size) with h | h | h
    · have hxl : lo ≤ x ∧ x < lo + l.size := ⟨hx.1, h⟩
      have hxr : ¬ (lo + l.size + 1 ≤ x ∧ x < lo + l.size + 1 + r.size) := by omega
      have hl : x - lo < l.size := by omega
      rw [ihl lo hxl hyl, edgeMovement_outside r _ x y hxr hyr]
      simp [Tree.depth, hl, Nat.add_comm]
    · have hxl : ¬ (lo ≤ x ∧ x < lo + l.size) := by omega
      have hxr : ¬ (lo + l.size + 1 ≤ x ∧ x < lo + l.size + 1 + r.size) := by omega
      have he : x - lo = l.size := by omega
      rw [edgeMovement_outside l _ x y hxl hyl, edgeMovement_outside r _ x y hxr hyr]
      simp [Tree.depth, he]
    · have hxl : ¬ (lo ≤ x ∧ x < lo + l.size) := by omega
      have hxr : lo + l.size + 1 ≤ x ∧ x < lo + l.size + 1 + r.size := by
        simp only [Tree.size] at hx; omega
      have hl : ¬ x - lo < l.size := by omega
      have he : x - lo ≠ l.size := by omega
      have hs : x - (lo + l.size + 1) = x - lo - l.size - 1 := by omega
      rw [edgeMovement_outside l _ x y hxl hyl, ihr _ hxr hyr]
      rw [hs]
      simp [Tree.depth, hl, he, Nat.add_comm]

/-- For two keys inside the subtree, the incoming edge is unused and the
boundary decomposition gives exactly their tree distance. -/
theorem edgeMovement_inside (t : Tree) (lo x y : Nat)
    (hx : lo ≤ x ∧ x < lo + t.size) (hy : lo ≤ y ∧ y < lo + t.size) :
    edgeMovement t lo x y = distance t (x - lo) (y - lo) := by
  induction t generalizing lo with
  | nil => simp [Tree.size] at hx; omega
  | node l r ihl ihr =>
    rw [edgeMovement_node]
    simp only [cut, hx, hy, iff_self, ↓reduceIte, Nat.zero_add]
    have hxl : (lo ≤ x ∧ x < lo + l.size) ↔ x < lo + l.size := by omega
    have hyl : (lo ≤ y ∧ y < lo + l.size) ↔ y < lo + l.size := by omega
    have hxr : (lo + l.size + 1 ≤ x ∧ x < lo + l.size + 1 + r.size) ↔ lo + l.size < x := by
      simp only [Tree.size] at hx; omega
    have hyr : (lo + l.size + 1 ≤ y ∧ y < lo + l.size + 1 + r.size) ↔ lo + l.size < y := by
      simp only [Tree.size] at hy; omega
    have ex : x - (lo + l.size + 1) = x - lo - l.size - 1 := by omega
    have ey : y - (lo + l.size + 1) = y - lo - l.size - 1 := by omega
    rcases lt_trichotomy x (lo + l.size) with hxL | hxE | hxR <;>
      rcases lt_trichotomy y (lo + l.size) with hyL | hyE | hyR
    · rw [ihl lo (hxl.mpr hxL) (hyl.mpr hyL), edgeMovement_outside r _ x y (by omega) (by omega)]
      simp only [distance, Tree.depth]
      split_ifs <;> omega
    · rw [edgeMovement_enter l lo x y (hxl.mpr hxL) (by omega),
        edgeMovement_outside r _ x y (by omega) (by omega)]
      simp only [distance, Tree.depth]
      split_ifs <;> omega
    · rw [edgeMovement_enter l lo x y (hxl.mpr hxL) (by omega), edgeMovement_symm r _ x y,
        edgeMovement_enter r _ y x (hyr.mpr hyR) (by omega)]
      rw [ey]
      simp only [distance, Tree.depth]
      split_ifs <;> omega
    · rw [edgeMovement_symm l lo x y, edgeMovement_enter l lo y x (hyl.mpr hyL) (by omega),
        edgeMovement_outside r _ x y (by omega) (by omega)]
      simp only [distance, Tree.depth]
      split_ifs <;> omega
    · rw [edgeMovement_outside l _ x y (by omega) (by omega),
        edgeMovement_outside r _ x y (by omega) (by omega)]
      simp only [distance, Tree.depth]
      split_ifs <;> omega
    · rw [edgeMovement_outside l _ x y (by omega) (by omega),
        edgeMovement_symm r _ x y, edgeMovement_enter r _ y x (hyr.mpr hyR) (by omega)]
      rw [ey]
      simp only [distance, Tree.depth]
      split_ifs <;> omega
    · rw [edgeMovement_symm l lo x y, edgeMovement_enter l lo y x (hyl.mpr hyL) (by omega),
        edgeMovement_enter r _ x y (hxr.mpr hxR) (by omega)]
      rw [ex]
      simp only [distance, Tree.depth]
      split_ifs <;> omega
    · rw [edgeMovement_outside l _ x y (by omega) (by omega),
        edgeMovement_enter r _ x y (hxr.mpr hxR) (by omega)]
      rw [ex]
      simp only [distance, Tree.depth]
      split_ifs <;> omega
    · rw [edgeMovement_outside l _ x y (by omega) (by omega), ihr _ (hxr.mpr hxR) (hyr.mpr hyR)]
      rw [ex, ey]
      simp only [distance, Tree.depth]
      split_ifs <;> omega

end RotationBST.LazyFinger
