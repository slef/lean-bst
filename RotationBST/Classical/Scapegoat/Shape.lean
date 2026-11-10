module

public import RotationBST.Classical.Scapegoat.Definitions.Abstract
public import RotationBST.Models.Dictionary.Depth
import Mathlib.Tactic

@[expose] public section

/-! Plain deletion and its certificate, and the imbalance potential `Φ = ∑ (|size l - size r| - 1)⁺`. -/
namespace RotationBST.Classical.Scapegoat
open Dictionary
open _root_.RotationBST.Tree (depth_left depth_root depth_right)

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

/-! ### The imbalance potential -/

/-- `|a - b| - 1`, truncated at zero. -/
def imb (a b : Nat) : Nat := (a - b) + (b - a) - 1

/-- `Φ`: the sum of the imbalances of all nodes. -/
def phi : Tree → Nat
  | .nil => 0
  | .node l r => imb l.size r.size + phi l + phi r

theorem phi_insertAt (t : Tree) (k : Nat) : phi (Tree.insertAt t k) ≤ phi t + (Tree.insertAt t k).depth k := by
  induction t generalizing k with
  | nil => simp [Tree.insertAt, phi, imb, Tree.size]
  | node l r il ir =>
    simp only [Tree.insertAt]; split
    · rename_i h
      have hs := insertAt_size l k
      have := il k
      rw [depth_left (by rw [hs]; omega)]
      simp only [phi, hs, imb]; omega
    · rename_i h
      have hs := insertAt_size r (k - l.size - 1)
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
