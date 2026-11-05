module

public import RotationBST.Bounds.LazyFinger.Geometry

@[expose] public section
namespace RotationBST.LazyFinger

private theorem shape_exists (n : Nat) : ∃ t : Tree, t.size = n := by
  induction n with
  | zero => exact ⟨.nil, rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨.node .nil t, by simp [Tree.size, ht, Nat.add_comm]⟩

theorem optimalCost_attained (n : Nat) (xs : List Nat) :
    ∃ t : Tree, t.size = n ∧ cost t xs = optimalCost n xs := by
  obtain ⟨t, ht⟩ := shape_exists n
  exact Nat.sInf_mem (show {k | ∃ u : Tree, u.size = n ∧ cost u xs = k}.Nonempty from
    ⟨cost t xs, t, ht, rfl⟩)

theorem optimalCost_le (t : Tree) (xs : List Nat) : optimalCost t.size xs ≤ cost t xs :=
  Nat.sInf_le ⟨t, rfl, rfl⟩

theorem length_le_optimalCost (n : Nat) (xs : List Nat) : xs.length ≤ optimalCost n xs := by
  obtain ⟨t, _, ht⟩ := optimalCost_attained n xs
  rw [← ht]
  cases t with
  | nil => exact le_rfl
  | node l r => exact length_le_costFrom _ _ _

theorem optimalCost_le_twice_static (t : Tree) (xs : List Nat) :
    optimalCost t.size xs ≤ 2 * StaticTree.cost t xs :=
  (optimalCost_le t xs).trans (cost_le_twice_static t xs)

theorem optimalCostFrom_attained (n p : Nat) (xs : List Nat) :
    ∃ t : Tree, t.size = n ∧ costFrom t p xs = optimalCostFrom n p xs := by
  obtain ⟨t, ht⟩ := shape_exists n
  exact Nat.sInf_mem (show {k | ∃ u : Tree, u.size = n ∧ costFrom u p xs = k}.Nonempty from
    ⟨costFrom t p xs, t, ht, rfl⟩)

theorem optimalCostFrom_le (t : Tree) (p : Nat) (xs : List Nat) :
    optimalCostFrom t.size p xs ≤ costFrom t p xs := Nat.sInf_le ⟨t, rfl, rfl⟩

end RotationBST.LazyFinger
