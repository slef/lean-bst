module

public import RotationBST.Structures.Treap.Random.Tree
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Treap.Random

/-- A common-ancestor event is a minimum over the hull of all three keys. -/
theorem common_ancestor_probability (w : Nat → ℝ) (n lo : Nat)
    (hw : ∀ k ∈ Finset.Ico lo (lo + n), 0 < w k) (T : List Nat → Tree)
    (spec : ∀ xs, (T xs).size = n ∧ Geometric.Heap xs.idxOf (T xs) lo)
    (a x y : Nat) (ha : lo ≤ a ∧ a < lo + n)
    (hx : lo ≤ x ∧ x < lo + n) (hy : lo ≤ y ∧ y < lo + n) :
    average w (Finset.Ico lo (lo + n))
      (fun xs => if a ∈ (T xs).searchPath lo x ∧ a ∈ (T xs).searchPath lo y then 1 else 0) =
      w a / (∑ k ∈ Finset.Icc (min a (min x y)) (max a (max x y)), w k) := by
  let u := Finset.Ico lo (lo + n)
  let s := Finset.Icc (min a (min x y)) (max a (max x y))
  have haS : a ∈ s := Finset.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩
  have sub : s ⊆ u := by
    intro k hk
    simp only [s, u, Finset.mem_Icc, Finset.mem_Ico] at *
    omega
  calc
    _ = firstProbability w u s a := by
      unfold firstProbability
      apply average_congr w u _ _ hw
      intro xs hxs
      have unique : Set.InjOn xs.idxOf (Set.Ico lo (lo + (T xs).size)) := by
        rw [(spec xs).1]
        simpa [u] using order_idxOf_injective hxs
      have haT : lo ≤ a ∧ a < lo + (T xs).size := by rw [(spec xs).1]; exact ha
      have hxT : lo ≤ x ∧ x < lo + (T xs).size := by rw [(spec xs).1]; exact hx
      have hyT : lo ≤ y ∧ y < lo + (T xs).size := by rw [(spec xs).1]; exact hy
      have heX := Geometric.heap_ancestor_iff xs.idxOf (T xs) lo a x
        (spec xs).2 unique haT hxT
      have heY := Geometric.heap_ancestor_iff xs.idxOf (T xs) lo a y
        (spec xs).2 unique haT hyT
      have hf := firstIn_eq_iff xs s a haS (by simpa [hxs.2] using sub)
      have he : (a ∈ (T xs).searchPath lo x ∧ a ∈ (T xs).searchPath lo y) ↔
          firstIn s xs = some a := by
        rw [heX, heY, hf]
        constructor
        · rintro ⟨hX, hY⟩ b hb
          have hb' := Finset.mem_Icc.mp hb
          have side : (min a x ≤ b ∧ b ≤ max a x) ∨ (min a y ≤ b ∧ b ≤ max a y) := by
            omega
          rcases side with h | h
          · exact hX b h.1 h.2
          · exact hY b h.1 h.2
        · intro h
          constructor <;> intro b hb hb' <;> apply h b <;>
            simp only [s, Finset.mem_Icc] <;> omega
      simp only [he]
    _ = _ := firstProbability_eq w u s a hw sub haS

end RotationBST.Treap.Random
