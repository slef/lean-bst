module

public import RotationBST.Algorithms.OptimalLazyFinger.Tabulation
public import RotationBST.Algorithms.OptimalLazyFinger.Preprocessing.Proofs
public import RotationBST.Bounds.LazyFinger.Optimal
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.OptimalLazyFinger
open LazyFinger

theorem optimize_spec (w : Nat → Nat → Nat) (n : Nat) :
    (optimize w n).1.size = n ∧
      intervalCost w (optimize w n).1 0 = (optimize w n).2 ∧
      ∀ t : Tree, t.size = n → (optimize w n).2 ≤ intervalCost w t 0 := by
  rw [optimize_eq_solve]
  exact solve_spec w n 0

theorem treeFrom_size (n p : Nat) (xs : List Nat) : (treeFrom n p xs).size = n :=
  (optimize_spec _ _).1

theorem prepared_intervalCost (n p : Nat) (xs : List Nat) (hp : p ≤ n)
    (valid : ∀ x ∈ xs, x < n) (t : Tree) (ht : t.size = n) :
    intervalCost (Preprocessing.toll (Preprocessing.prepare (n + 1) p xs) (n + 1)) t 0 =
      intervalCost (fun a b => crossings a b p xs) t 0 := by
  apply intervalCost_congr _ _ t 0 n (by omega)
  intro a b _ hab hb
  exact Preprocessing.toll_prepare (n + 1) p xs (by omega)
    (fun x hx => by have := valid x hx; omega) a b hab (by omega)

theorem treeFrom_minimal (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) (t : Tree) (ht : t.size = n) :
    costFrom (treeFrom n p xs) p xs ≤ costFrom t p xs := by
  have hs := treeFrom_size n p xs
  have hb := optimize_spec (Preprocessing.toll (Preprocessing.prepare (n + 1) p xs) (n + 1)) n
  have hc := hb.2.2 t ht
  rw [← hb.2.1] at hc
  change intervalCost (Preprocessing.toll (Preprocessing.prepare (n + 1) p xs) (n + 1))
    (treeFrom n p xs) 0 ≤ _ at hc
  rw [prepared_intervalCost n p xs (by omega) valid _ hs,
    prepared_intervalCost n p xs (by omega) valid t ht] at hc
  rw [costFrom_eq_crossings _ p xs (by omega) (by simpa [hs] using valid),
    costFrom_eq_crossings t p xs (by omega) (by simpa [ht] using valid)]
  omega

theorem treeFrom_optimal (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    costFrom (treeFrom n p xs) p xs = optimalCostFrom n p xs := by
  obtain ⟨t, ht, hc⟩ := optimalCostFrom_attained n p xs
  have hi := treeFrom_minimal n p xs hp valid t ht
  rw [hc] at hi
  have hj := optimalCostFrom_le (treeFrom n p xs) p xs
  rw [treeFrom_size] at hj
  exact Nat.le_antisymm hi hj

theorem tree_size (n : Nat) (xs : List Nat) : (tree n xs).size = n := treeFrom_size _ _ _

theorem tree_minimal (n : Nat) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < n) (t : Tree) (ht : t.size = n) :
    cost (tree n xs) xs ≤ cost t xs := by
  have hs := tree_size n xs
  have hb := optimize_spec (Preprocessing.toll (Preprocessing.prepare (n + 1) n xs) (n + 1)) n
  have hc := hb.2.2 t ht
  rw [← hb.2.1] at hc
  change intervalCost (Preprocessing.toll (Preprocessing.prepare (n + 1) n xs) (n + 1))
    (tree n xs) 0 ≤ _ at hc
  rw [prepared_intervalCost n n xs le_rfl valid _ hs,
    prepared_intervalCost n n xs le_rfl valid t ht] at hc
  have hl := cost_eq_crossings (tree n xs) xs (by simpa [hs] using valid)
  have hr := cost_eq_crossings t xs (by simpa [ht] using valid)
  rw [hs] at hl
  rw [ht] at hr
  omega

/-- Exact optimality for the original root-start benchmark, including the
empty universe, repeated requests, and initialization. -/
theorem tree_optimal (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    cost (tree n xs) xs = optimalCost n xs := by
  obtain ⟨t, ht, hc⟩ := optimalCost_attained n xs
  have hi := tree_minimal n xs valid t ht
  rw [hc] at hi
  have hj := optimalCost_le (tree n xs) xs
  rw [tree_size] at hj
  exact Nat.le_antisymm hi hj

end RotationBST.OptimalLazyFinger
