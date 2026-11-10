module

public import RotationBST.Classical.Random.Abstract
public import RotationBST.Structures.Treap.Order.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.RandomTrees
open Classical.Random

-- Some treap exists for every order (ties are allowed by `Heap`), so the
-- hypothesis of `expected_depth` can always be met.
noncomputable def treap (n : Nat) (xs : List Nat) : Tree :=
  (Geometric.TreapOrder.Results.exists_tree xs.idxOf n 0).choose

theorem treap_spec (n : Nat) (xs : List Nat) :
    (treap n xs).size = n ∧ Geometric.Heap xs.idxOf (treap n xs) 0 :=
  (Geometric.TreapOrder.Results.exists_tree xs.idxOf n 0).choose_spec

-- The root key 0 of 3 keys: H(1) + H(3) - 2 = 1 + 11/6 - 2 = 5/6.
example : Treap.Random.average (fun _ => 1) (Finset.range 3)
    (fun xs => ((treap 3 xs).depth 0 : ℝ)) = 5 / 6 := by
  rw [Results.expected_depth 3 0 (by decide) (treap 3) (treap_spec 3)]
  norm_num [harmonic]

-- The middle key of 3 keys: H(2) + H(2) - 2 = 1.
example : Treap.Random.average (fun _ => 1) (Finset.range 3)
    (fun xs => ((treap 3 xs).depth 1 : ℝ)) = 1 := by
  rw [Results.expected_depth 3 1 (by decide) (treap 3) (treap_spec 3)]
  norm_num [harmonic]

example (n x : Nat) (hx : x < n) : Treap.Random.average (fun _ => 1) (Finset.range n)
    (fun xs => ((treap n xs).depth x : ℝ)) ≤ 2 * Real.log n :=
  Results.expected_depth_le n x hx (treap n) (treap_spec n)

end RotationBST.Tests.RandomTrees
