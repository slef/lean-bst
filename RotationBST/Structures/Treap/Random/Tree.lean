module

public import RotationBST.Structures.Treap.Random.Orders
public import RotationBST.Structures.Treap.Random.Minimum
public import RotationBST.Structures.Treap.Order.Abstract
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Treap.Random

/-- A concrete family of treap shapes, sampled by the finite priority-order
process, has the usual weighted ancestor probability. This supplies the
randomized construction rather than assuming an ancestor-probability oracle. -/
theorem exists_random_treap (w : Nat → ℝ) (n lo : Nat)
    (hw : ∀ k ∈ Finset.Ico lo (lo + n), 0 < w k) :
    ∃ T : List Nat → Tree,
      (∀ xs, (T xs).size = n ∧ Geometric.Heap xs.idxOf (T xs) lo) ∧
      (∀ a x, lo ≤ a → a < lo + n → lo ≤ x → x < lo + n →
        average w (Finset.Ico lo (lo + n))
          (fun xs => if a ∈ (T xs).searchPath lo x then 1 else 0) =
        w a / (∑ k ∈ Finset.Icc (min a x) (max a x), w k)) := by
  classical
  let T : List Nat → Tree := fun xs => Classical.choose (Geometric.heap_exists xs.idxOf n lo)
  have spec (xs : List Nat) : (T xs).size = n ∧ Geometric.Heap xs.idxOf (T xs) lo :=
    Classical.choose_spec (Geometric.heap_exists xs.idxOf n lo)
  refine ⟨T, spec, ?_⟩
  intro a x ha ha' hx hx'
  let u := Finset.Ico lo (lo + n)
  let s := Finset.Icc (min a x) (max a x)
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
      have haT : lo ≤ a ∧ a < lo + (T xs).size := by rw [(spec xs).1]; exact ⟨ha, ha'⟩
      have hxT : lo ≤ x ∧ x < lo + (T xs).size := by rw [(spec xs).1]; exact ⟨hx, hx'⟩
      have he := Geometric.heap_ancestor_iff xs.idxOf (T xs) lo a x
        (spec xs).2 unique haT hxT
      have hf := firstIn_eq_iff xs s a haS (by simpa [hxs.2] using sub)
      have heq : a ∈ (T xs).searchPath lo x ↔ firstIn s xs = some a := by
        rw [he, hf]
        simp only [s, Finset.mem_Icc, and_imp]
      simp only [heq]
    _ = _ := firstProbability_eq w u s a hw sub haS

end RotationBST.Treap.Random
