module

public import RotationBST.Classical.RankBalanced.Insertion.Definitions.Abstract
public import RotationBST.Models.Dictionary.Basic
import Mathlib.Tactic

@[expose] public section

/-! Insertion is a dictionary step: a leaf is spliced in, then the rotations
and rank changes counted by `insert` are performed. -/
namespace RotationBST.Classical.RankBalanced
open Dictionary

theorem fixLeft_moves (l' : RankedTree) (k : Int) (r : RankedTree) (a e : Nat) :
    ∃ da de, Moves (.node l' k r) (fixLeft l' k r a e).1 da de ∧
      (fixLeft l' k r a e).2.1 = a + da ∧ (fixLeft l' k r a e).2.2 = e + de := by
  unfold fixLeft
  split
  · exact ⟨0, 0, .refl, rfl, rfl⟩
  · split
    · exact ⟨0, 1, .edit .here .refl, rfl, rfl⟩
    · split
      · rename_i x kx y
        split
        · exact ⟨1, 1, .rotate .right (.edit (.inRight .here) .refl), rfl, rfl⟩
        · split
          · rename_i y₁ ky y₂
            exact ⟨2, 3, .rotate (.inLeft .left) (.rotate .right
              (.edit .here (.edit (.inLeft .here) (.edit (.inRight .here) .refl)))), rfl, rfl⟩
          · exact ⟨0, 0, .refl, rfl, rfl⟩
      · exact ⟨0, 0, .refl, rfl, rfl⟩

theorem fixRight_moves (l : RankedTree) (k : Int) (r' : RankedTree) (a e : Nat) :
    ∃ da de, Moves (.node l k r') (fixRight l k r' a e).1 da de ∧
      (fixRight l k r' a e).2.1 = a + da ∧ (fixRight l k r' a e).2.2 = e + de := by
  unfold fixRight
  split
  · exact ⟨0, 0, .refl, rfl, rfl⟩
  · split
    · exact ⟨0, 1, .edit .here .refl, rfl, rfl⟩
    · split
      · rename_i y ky z
        split
        · exact ⟨1, 1, .rotate .left (.edit (.inLeft .here) .refl), rfl, rfl⟩
        · split
          · rename_i y₁ kyy y₂
            exact ⟨2, 3, .rotate (.inRight .right) (.rotate .left
              (.edit .here (.edit (.inLeft .here) (.edit (.inRight .here) .refl)))), rfl, rfl⟩
          · exact ⟨0, 0, .refl, rfl, rfl⟩
      · exact ⟨0, 0, .refl, rfl, rfl⟩

theorem insert_moves (t : RankedTree) (g : Nat) :
    Moves (t.insertAt g 0) (insert t g).1 (insert t g).2.1 (insert t g).2.2 := by
  induction t generalizing g with
  | nil => exact .refl
  | node l k r il ir =>
    simp only [LabelledTree.insertAt, insert]
    split
    · obtain ⟨da, de, m, ha, he⟩ := fixLeft_moves (insert l g).1 k r (insert l g).2.1 (insert l g).2.2
      rw [ha, he]
      exact ((il g).inLeft k r).append m
    · obtain ⟨da, de, m, ha, he⟩ := fixRight_moves l k (insert r (g - l.erase.size - 1)).1
        (insert r (g - l.erase.size - 1)).2.1 (insert r (g - l.erase.size - 1)).2.2
      rw [ha, he]
      exact ((ir _).inRight l k).append m

/-- Insertion is a dictionary step: main cost `1 + depth` of the new leaf plus
rotations, and one data edit per rank change. -/
theorem insert_step (t : RankedTree) (g : Nat) (hg : g ≤ t.erase.size) :
    Step t (.insert g) (insert t g).1 ((t.insertAt g 0).erase.depth g + 1 + (insert t g).2.1) (insert t g).2.2 := by
  have := Step.insert (s := t) (k := g) hg .refl (insertAt_splice t g 0 hg) (insert_moves t g)
  simpa using this

theorem insert_size (t : RankedTree) (g : Nat) : (insert t g).1.erase.size = t.erase.size + 1 := by
  have := (insert_moves t g).size
  rw [insertAt_erase_size] at this; omega

end RotationBST.Classical.RankBalanced
