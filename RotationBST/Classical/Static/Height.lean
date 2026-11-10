module

public import RotationBST.Classical.Static.Balanced
import Mathlib.Tactic

@[expose] public section

/-! Height: the balanced tree has the minimum height `⌊log₂ n⌋ + 1`. -/
namespace RotationBST.Classical.Static

theorem depth_lt_height (t : Tree) (x : Nat) (hx : x < t.size) : t.depth x < height t := by
  induction t generalizing x with
  | nil => simp [Tree.size] at hx
  | node l r il ir =>
    simp only [Tree.depth, height]
    split
    · have := il x (by assumption); omega
    · split
      · omega
      · have := ir (x - l.size - 1) (by simp [Tree.size] at hx; omega); omega

theorem height_le_of_depth (t : Tree) (h : Nat) (hd : ∀ x < t.size, t.depth x ≤ h) :
    height t ≤ h + 1 := by
  induction t generalizing h with
  | nil => simp [height]
  | node l r il ir =>
    simp only [height]
    have h0 := hd l.size (by simp [Tree.size]; omega)
    simp only [Tree.depth, lt_irrefl, ↓reduceIte] at h0
    cases h with
    | zero =>
      -- Every key is at the root: both children are empty.
      have hl : l.size = 0 := by
        by_contra hne
        have := hd 0 (by simp [Tree.size])
        simp only [Tree.depth, show 0 < l.size by omega, ↓reduceIte] at this; omega
      have hr : r.size = 0 := by
        by_contra hne
        have := hd (l.size + 1) (by simp [Tree.size]; omega)
        simp only [Tree.depth, show ¬ l.size + 1 < l.size by omega,
          show l.size + 1 ≠ l.size by omega, ↓reduceIte] at this; omega
      cases l with
      | node => simp [Tree.size] at hl
      | nil => cases r with
        | node => simp [Tree.size] at hr
        | nil => simp [height]
    | succ h =>
      have hl := il h fun x hx => by
        have := hd x (by simp [Tree.size]; omega)
        simp only [Tree.depth, hx, ↓reduceIte] at this; omega
      have hr := ir h fun x hx => by
        have := hd (l.size + 1 + x) (by simp [Tree.size]; omega)
        simp only [Tree.depth, show ¬ l.size + 1 + x < l.size by omega,
          show l.size + 1 + x ≠ l.size by omega, ↓reduceIte,
          show l.size + 1 + x - l.size - 1 = x by omega] at this; omega
      omega

/-- Every nonempty tree has height at least `⌊log₂ n⌋ + 1`. -/
theorem log2_lt_height (t : Tree) (h : 0 < t.size) : Nat.log2 t.size + 1 ≤ height t := by
  obtain ⟨x, hx, hd⟩ := exists_deep t h
  have := depth_lt_height t x hx
  omega

theorem balanced_height (n : Nat) (h : 0 < n) : height (balanced n) = Nat.log2 n + 1 := by
  apply le_antisymm
  · exact height_le_of_depth _ _ fun x hx => balanced_depth n x (by rwa [balanced_size] at hx)
  · have := log2_lt_height (balanced n) (by rwa [balanced_size])
    rwa [balanced_size] at this

end RotationBST.Classical.Static
