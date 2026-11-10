module

public import RotationBST.Classical.Scapegoat.Definitions.Abstract
public import RotationBST.Models.Dictionary.Basic
import Mathlib.Tactic

@[expose] public section

/-! Plain insertion and deletion: sizes, dictionary certificates, depths, and
the imbalance potential `Φ = ∑ (|size l - size r| - 1)⁺`. -/
namespace RotationBST.Classical.Scapegoat
open Dictionary

/-! ### Insertion of a leaf -/

theorem insertLeaf_size (t : Tree) (k : Nat) : (insertLeaf t k).size = t.size + 1 := by
  induction t generalizing k with
  | nil => simp [insertLeaf, Tree.size]
  | node l r il ir =>
    simp only [insertLeaf]; split
    · simp only [Tree.size, il]; omega
    · simp only [Tree.size, ir]; omega

theorem insertLeaf_splice (t : Tree) (k : Nat) (hk : k ≤ t.size) :
    Splice (insertLeaf t k).unit k t.unit := by
  induction t generalizing k with
  | nil =>
    have : k = 0 := by simp [Tree.size] at hk; omega
    subst this; exact .noLeft
  | node l r il ir =>
    simp only [insertLeaf]; split
    · exact .inLeft (il k (by assumption))
    · rename_i h
      have := Splice.inRight (l := l.unit) (d := ()) (ir (k - l.size - 1) (by simp [Tree.size] at hk; omega))
      simp only [unit_erase] at this
      rwa [show l.size + 1 + (k - l.size - 1) = k by omega] at this

theorem insertLeaf_depth_lt (t : Tree) (k x : Nat) (hx : x < t.size) (hk : x < k) :
    (insertLeaf t k).depth x = t.depth x := by
  induction t generalizing k x with
  | nil => simp [Tree.size] at hx
  | node l r il ir =>
    simp only [insertLeaf]
    split
    · rename_i hkl
      have hs := insertLeaf_size l k
      rw [depth_left (show x < (insertLeaf l k).size by omega), depth_left (by omega), il k x (by omega) hk]
    · rename_i hkl
      by_cases h1 : x < l.size
      · rw [depth_left h1, depth_left h1]
      · by_cases h2 : x = l.size
        · rw [depth_root h2, depth_root h2]
        · rw [depth_right (by omega), depth_right (by omega),
            ir (k - l.size - 1) (x - l.size - 1) (by simp [Tree.size] at hx; omega) (by omega)]

theorem insertLeaf_depth_ge (t : Tree) (k x : Nat) (hx : x < t.size) (hk : k ≤ x) :
    (insertLeaf t k).depth (x + 1) = t.depth x := by
  induction t generalizing k x with
  | nil => simp [Tree.size] at hx
  | node l r il ir =>
    simp only [insertLeaf]
    split
    · rename_i hkl
      have hs := insertLeaf_size l k
      by_cases h1 : x < l.size
      · rw [depth_left (show x + 1 < (insertLeaf l k).size by omega), depth_left h1, il k x h1 hk]
      · by_cases h2 : x = l.size
        · rw [depth_root (show x + 1 = (insertLeaf l k).size by omega), depth_root h2]
        · rw [depth_right (show (insertLeaf l k).size < x + 1 by omega), depth_right (by omega), hs,
            show x + 1 - (l.size + 1) - 1 = x - l.size - 1 by omega]
    · rename_i hkl
      have hx' : l.size < x := by
        by_contra hc; omega
      rw [depth_right (show l.size < x + 1 by omega), depth_right hx',
        show x + 1 - l.size - 1 = (x - l.size - 1) + 1 by omega,
        ir (k - l.size - 1) (x - l.size - 1) (by simp [Tree.size] at hx; omega) (by omega)]

/-- Every other key of the new tree is an old key at the same depth. -/
theorem insertLeaf_depth_other (t : Tree) (k z : Nat) (hk : k ≤ t.size) (hz : z < t.size + 1) (hzk : z ≠ k) :
    ∃ x < t.size, (insertLeaf t k).depth z = t.depth x := by
  by_cases h : z < k
  · exact ⟨z, by omega, insertLeaf_depth_lt t k z (by omega) h⟩
  · refine ⟨z - 1, by omega, ?_⟩
    have := insertLeaf_depth_ge t k (z - 1) (by omega) (by omega)
    rwa [show z - 1 + 1 = z by omega] at this

/-- The new leaf hangs below an old key. -/
theorem insertLeaf_parent (t : Tree) (k : Nat) (hk : k ≤ t.size) (ht : t ≠ .nil) :
    ∃ x < t.size, (insertLeaf t k).depth k = t.depth x + 1 := by
  induction t generalizing k with
  | nil => exact absurd rfl ht
  | node l r il ir =>
    simp only [insertLeaf]; split
    · rename_i h
      have hs := insertLeaf_size l k
      rw [depth_left (by rw [hs]; omega)]
      cases l with
      | nil =>
        refine ⟨0, by simp [Tree.size], ?_⟩
        simp [insertLeaf, Tree.depth, Tree.size] at h ⊢; omega
      | node a b =>
        obtain ⟨x, hx, he⟩ := il k h (by simp)
        exact ⟨x, by simp only [Tree.size] at hx ⊢; omega, by rw [he, depth_left hx]⟩
    · rename_i h
      have hs := insertLeaf_size r (k - l.size - 1)
      rw [depth_right (by omega)]
      cases r with
      | nil =>
        refine ⟨l.size, by simp [Tree.size], ?_⟩
        rw [depth_root rfl]
        have : k - l.size - 1 = 0 := by simp [Tree.size] at hk; omega
        simp [this, insertLeaf, Tree.depth, Tree.size]
      | node a b =>
        obtain ⟨x, hx, he⟩ := ir (k - l.size - 1) (by simp [Tree.size] at hk ⊢; omega) (by simp)
        refine ⟨l.size + 1 + x, by simp only [Tree.size] at hx ⊢; omega, ?_⟩
        rw [he, depth_right (l := l) (by omega), show l.size + 1 + x - l.size - 1 = x by omega]

/-! ### Plain deletion -/

theorem deleteTarget_zero (t : Tree) (ht : t ≠ .nil) : deleteTarget t 0 = 0 := by
  induction t with
  | nil => exact absurd rfl ht
  | node a b ia _ =>
    cases a with
    | nil => simp [deleteTarget, Tree.size]
    | node c d =>
      have h0 : 0 < (Tree.node c d).size := by simp [Tree.size]
      simp only [deleteTarget, h0, ↓reduceIte]
      exact ia (by simp)

theorem bstDelete_splice (t : Tree) (x : Nat) (hx : x < t.size) :
    Splice t.unit (deleteTarget t x) (bstDelete t x).unit ∧
      (deleteTarget t x = x ∨ (t.TwoChildren x ∧ deleteTarget t x = x + 1)) := by
  induction t generalizing x with
  | nil => simp [Tree.size] at hx
  | node l r il ir =>
    by_cases h1 : x < l.size
    · obtain ⟨sp, hc⟩ := il x h1
      simp only [bstDelete, deleteTarget, h1, ↓reduceIte]
      refine ⟨.inLeft sp, ?_⟩
      simpa [Tree.TwoChildren, h1] using hc
    · by_cases h2 : x = l.size
      · subst h2
        cases l with
        | nil =>
          simp only [bstDelete, deleteTarget, Tree.size, lt_irrefl, ↓reduceIte]
          exact ⟨.noLeft, by simp⟩
        | node a b =>
          cases r with
          | nil =>
            simp only [bstDelete, deleteTarget, lt_irrefl, ↓reduceIte]
            have := Splice.noRight (l := (Tree.node a b).unit) (d := ())
            simp only [unit_erase] at this
            exact ⟨this, by simp⟩
          | node c d =>
            simp only [bstDelete, deleteTarget, lt_irrefl, ↓reduceIte]
            obtain ⟨sp, _⟩ := ir 0 (by simp [Tree.size])
            rw [deleteTarget_zero _ (by simp)] at sp
            have := Splice.inRight (l := (Tree.node a b).unit) (d := ()) sp
            simp only [unit_erase, Nat.add_zero] at this
            exact ⟨this, Or.inr ⟨by simp [Tree.TwoChildren], by simp⟩⟩
      · obtain ⟨sp, hc⟩ := ir (x - l.size - 1) (by simp [Tree.size] at hx; omega)
        simp only [bstDelete, deleteTarget, h1, h2, ↓reduceIte]
        have := Splice.inRight (l := l.unit) (d := ()) sp
        simp only [unit_erase] at this
        refine ⟨this, ?_⟩
        rcases hc with hc | ⟨ht, hc⟩
        · left; omega
        · right; exact ⟨by simp [Tree.TwoChildren, h1, h2, ht], by omega⟩

theorem bstDelete_size (t : Tree) (x : Nat) (hx : x < t.size) : (bstDelete t x).size = t.size - 1 := by
  have := (bstDelete_splice t x hx).1.size
  simp only [unit_erase] at this; omega

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

/-! ### The imbalance potential -/

/-- `|a - b| - 1`, truncated at zero. -/
def imb (a b : Nat) : Nat := (a - b) + (b - a) - 1

/-- `Φ`: the sum of the imbalances of all nodes. -/
def phi : Tree → Nat
  | .nil => 0
  | .node l r => imb l.size r.size + phi l + phi r

theorem phi_insertLeaf (t : Tree) (k : Nat) : phi (insertLeaf t k) ≤ phi t + (insertLeaf t k).depth k := by
  induction t generalizing k with
  | nil => simp [insertLeaf, phi, imb, Tree.size]
  | node l r il ir =>
    simp only [insertLeaf]; split
    · rename_i h
      have hs := insertLeaf_size l k
      have := il k
      rw [depth_left (by rw [hs]; omega)]
      simp only [phi, hs, imb]; omega
    · rename_i h
      have hs := insertLeaf_size r (k - l.size - 1)
      have := ir (k - l.size - 1)
      rw [depth_right (by omega)]
      simp only [phi, hs, imb]; omega

theorem phi_splice {α : Type} {t u : LabelledTree α} {y : Nat} (h : Splice t y u) :
    phi u.erase ≤ phi t.erase + t.erase.depth y := by
  induction h with
  | noLeft => simp only [LabelledTree.erase, phi, Tree.size, imb]; omega
  | noRight => simp only [LabelledTree.erase, phi, Tree.size, imb]; omega
  | inLeft sp ih =>
    rename_i l l' r d x
    have hs := sp.size
    simp only [LabelledTree.erase, phi, imb] at ih ⊢
    rw [depth_left (by omega)]; omega
  | inRight sp ih =>
    rename_i l r r' d x
    have hs := sp.size
    simp only [LabelledTree.erase, phi, imb] at ih ⊢
    rw [depth_right (by omega), show l.erase.size + 1 + x - l.erase.size - 1 = x by omega]; omega

end RotationBST.Classical.Scapegoat
