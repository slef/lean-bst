module

public import RotationBST.Models.Region.Basic
import Mathlib.Data.Set.Finite.Lemmas
public import RotationBST.Models.Region.Defs

@[expose] public section
namespace RotationBST.Region
open Pointer.Lazy.Skeleton

/-- Rearrange only the active region into heap order, keeping every fringe
subtree unchanged. Planning this rearrangement is uncharged in the BST model. -/
theorem heapify (priority : Nat → WithTop Nat) (s : Region) (lo : Nat) :
    ∃ t : Region, Same s t lo ∧ ActiveHeap priority t lo := by
  classical
  suffices ∀ n, ∀ s : Region, s.size = n → ∀ lo,
      ∃ t : Region, Same s t lo ∧ ActiveHeap priority t lo from this s.size s rfl lo
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro s hs lo
    cases s with
    | hole tree => exact ⟨.hole tree, Same.refl _ _, trivial⟩
    | node l r =>
      have nonempty : (keys (.node l r) lo).Nonempty :=
        ⟨lo + l.tree.size, Finset.mem_insert_self ..⟩
      obtain ⟨x, hx, hmin⟩ := (keys (.node l r) lo).exists_min_image priority nonempty
      obtain ⟨a, b, hab, hroot⟩ := expose (.node l r) lo x hx
      have hsizes := hab.size
      obtain ⟨a', ha, hha⟩ := ih a.size (by simp only [size] at hsizes hs; omega) a rfl lo
      obtain ⟨b', hb, hhb⟩ := ih b.size (by simp only [size] at hsizes hs; omega) b rfl
        (lo + a.tree.size + 1)
      have same := hab.trans (same_node ha hb)
      refine ⟨.node a' b', same, ?_, hha, ?_⟩
      · intro y hy
        have hy' : y ∈ keys (.node l r) lo := by rw [same.2.1]; exact hy
        have root' : lo + a'.tree.size = x := by rw [← ha.1]; exact hroot
        rw [root']
        exact hmin y hy'
      · simpa only [← ha.1] using hhb

end RotationBST.Region
