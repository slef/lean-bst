module

public import RotationBST.Models.Dictionary.Basic
import Mathlib.Tactic

@[expose] public section

/-! Depths around a plain leaf insertion (`Tree.insertAt`) and a splice. -/
namespace RotationBST.Dictionary
open _root_.RotationBST.Tree (depth_left depth_root depth_right)

/-! ### Insertion of a leaf -/

theorem insertAt_depth_lt (t : Tree) (k x : Nat) (hx : x < t.size) (hk : x < k) :
    (Tree.insertAt t k).depth x = t.depth x := by
  induction t generalizing k x with
  | nil => simp [Tree.size] at hx
  | node l r il ir =>
    simp only [Tree.insertAt]
    split
    · rename_i hkl
      have hs := insertAt_size l k
      rw [depth_left (show x < (Tree.insertAt l k).size by omega), depth_left (by omega), il k x (by omega) hk]
    · rename_i hkl
      by_cases h1 : x < l.size
      · rw [depth_left h1, depth_left h1]
      · by_cases h2 : x = l.size
        · rw [depth_root h2, depth_root h2]
        · rw [depth_right (by omega), depth_right (by omega),
            ir (k - l.size - 1) (x - l.size - 1) (by simp [Tree.size] at hx; omega) (by omega)]

theorem insertAt_depth_ge (t : Tree) (k x : Nat) (hx : x < t.size) (hk : k ≤ x) :
    (Tree.insertAt t k).depth (x + 1) = t.depth x := by
  induction t generalizing k x with
  | nil => simp [Tree.size] at hx
  | node l r il ir =>
    simp only [Tree.insertAt]
    split
    · rename_i hkl
      have hs := insertAt_size l k
      by_cases h1 : x < l.size
      · rw [depth_left (show x + 1 < (Tree.insertAt l k).size by omega), depth_left h1, il k x h1 hk]
      · by_cases h2 : x = l.size
        · rw [depth_root (show x + 1 = (Tree.insertAt l k).size by omega), depth_root h2]
        · rw [depth_right (show (Tree.insertAt l k).size < x + 1 by omega), depth_right (by omega), hs,
            show x + 1 - (l.size + 1) - 1 = x - l.size - 1 by omega]
    · rename_i hkl
      have hx' : l.size < x := by
        by_contra hc; omega
      rw [depth_right (show l.size < x + 1 by omega), depth_right hx',
        show x + 1 - l.size - 1 = (x - l.size - 1) + 1 by omega,
        ir (k - l.size - 1) (x - l.size - 1) (by simp [Tree.size] at hx; omega) (by omega)]

/-- Every other key of the new tree is an old key at the same depth. -/
theorem insertAt_depth_other (t : Tree) (k z : Nat) (hk : k ≤ t.size) (hz : z < t.size + 1) (hzk : z ≠ k) :
    ∃ x < t.size, (Tree.insertAt t k).depth z = t.depth x := by
  by_cases h : z < k
  · exact ⟨z, by omega, insertAt_depth_lt t k z (by omega) h⟩
  · refine ⟨z - 1, by omega, ?_⟩
    have := insertAt_depth_ge t k (z - 1) (by omega) (by omega)
    rwa [show z - 1 + 1 = z by omega] at this

/-- The new leaf hangs below an old key. -/
theorem insertAt_parent (t : Tree) (k : Nat) (hk : k ≤ t.size) (ht : t ≠ .nil) :
    ∃ x < t.size, (Tree.insertAt t k).depth k = t.depth x + 1 := by
  induction t generalizing k with
  | nil => exact absurd rfl ht
  | node l r il ir =>
    simp only [Tree.insertAt]; split
    · rename_i h
      have hs := insertAt_size l k
      rw [depth_left (by rw [hs]; omega)]
      cases l with
      | nil =>
        refine ⟨0, by simp [Tree.size], ?_⟩
        simp [Tree.insertAt, Tree.depth, Tree.size] at h ⊢; omega
      | node a b =>
        obtain ⟨x, hx, he⟩ := il k h (by simp)
        exact ⟨x, by simp only [Tree.size] at hx ⊢; omega, by rw [he, depth_left hx]⟩
    · rename_i h
      have hs := insertAt_size r (k - l.size - 1)
      rw [depth_right (by omega)]
      cases r with
      | nil =>
        refine ⟨l.size, by simp [Tree.size], ?_⟩
        rw [depth_root rfl]
        have : k - l.size - 1 = 0 := by simp [Tree.size] at hk; omega
        simp [this, Tree.insertAt, Tree.depth, Tree.size]
      | node a b =>
        obtain ⟨x, hx, he⟩ := ir (k - l.size - 1) (by simp [Tree.size] at hk ⊢; omega) (by simp)
        refine ⟨l.size + 1 + x, by simp only [Tree.size] at hx ⊢; omega, ?_⟩
        rw [he, depth_right (l := l) (by omega), show l.size + 1 + x - l.size - 1 = x by omega]

/-! ### Depths under a splice -/

theorem splice_depth {α : Type} {t u : LabelledTree α} {y : Nat} (h : Splice t y u) :
    ∀ z < u.erase.size, ∃ z₀ < t.erase.size, u.erase.depth z ≤ t.erase.depth z₀ := by
  induction h with
  | noLeft =>
    rename_i d r
    intro z hz
    refine ⟨z + 1, by simp [LabelledTree.erase, Tree.size]; omega, ?_⟩
    simp only [LabelledTree.erase]
    rw [depth_right (by simp [Tree.size])]; simp [Tree.size]
  | noRight =>
    rename_i l d
    intro z hz
    refine ⟨z, by simp [LabelledTree.erase, Tree.size]; omega, ?_⟩
    simp only [LabelledTree.erase]
    rw [depth_left hz]; omega
  | inLeft sp ih =>
    rename_i l l' r d x
    have hs := sp.size
    intro z hz
    simp only [LabelledTree.erase, Tree.size] at hz ⊢
    by_cases h1 : z < l'.erase.size
    · obtain ⟨z₀, h₀, hd⟩ := ih z h1
      exact ⟨z₀, by omega, by rw [depth_left h1, depth_left h₀]; omega⟩
    · by_cases h2 : z = l'.erase.size
      · exact ⟨l.erase.size, by omega, by rw [depth_root h2]; omega⟩
      · refine ⟨z + 1, by omega, ?_⟩
        rw [depth_right (by omega), depth_right (by omega),
          show z + 1 - l.erase.size - 1 = z - l'.erase.size - 1 by omega]
  | inRight sp ih =>
    rename_i l r r' d x
    have hs := sp.size
    intro z hz
    simp only [LabelledTree.erase, Tree.size] at hz ⊢
    by_cases h1 : z < l.erase.size
    · exact ⟨z, by omega, by rw [depth_left h1, depth_left h1]⟩
    · by_cases h2 : z = l.erase.size
      · exact ⟨z, by omega, by rw [depth_root h2]; omega⟩
      · obtain ⟨z₀, h₀, hd⟩ := ih (z - l.erase.size - 1) (by omega)
        refine ⟨l.erase.size + 1 + z₀, by omega, ?_⟩
        rw [depth_right (by omega), depth_right (by omega),
          show l.erase.size + 1 + z₀ - l.erase.size - 1 = z₀ by omega]; omega

end RotationBST.Dictionary
