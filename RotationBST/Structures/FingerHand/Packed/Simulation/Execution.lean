module

public import RotationBST.Structures.FingerHand.Packed.Simulation.Instructions

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- A request is implemented by simulating its before/after instructions and
visiting the requested key at the chosen represented finger. The request unit
and both directions of navigation are charged. -/
theorem simulate_serves {fingers : Nat} {h : Hand} {s t : Multifinger.State fingers}
    {x cost : Nat} (rep : h.Represents s) (valid : s.Valid) (request : Multifinger.Serves s t x cost) :
    ∃ (after : Hand) (k : Nat), after.Represents t ∧ Pointer.Serves h.tree after.tree x k ∧
      k + after.potential ≤ (344 + 60 * (fingers + 1)) * cost + h.potential := by
  obtain ⟨visited, before, after, i, first, requested, last, rfl⟩ := request
  obtain ⟨middle, k, middleRep, beginTrace, beginCost⟩ := simulate_trace rep valid first
  have middleValid := first.valid valid
  obtain ⟨cursor, navigation, outward, key, inward, navigationCost⟩ := middleRep.visit middleValid i
  obtain ⟨final, m, target, endTrace, endCost⟩ := simulate_trace middleRep middleValid last
  refine ⟨final, 1 + (k + navigation) + (navigation + m), target,
    ⟨cursor, ⟨final.tree, []⟩, k + navigation, navigation + m,
      beginTrace.append outward, requested ▸ key, inward.append endTrace, rfl, rfl⟩, ?_⟩
  simp only [Nat.mul_add, Nat.mul_one] at beginCost endCost ⊢
  omega

/-- A complete multifinger request execution has a conventional one-pointer
execution serving the same request sequence. The final hand retains every
finger position and the amortized bounds telescope across requests. -/
theorem simulate_execution {fingers : Nat} {h : Hand} {s t : Multifinger.State fingers}
    {xs : List Nat} {cost : Nat} (rep : h.Represents s) (valid : s.Valid)
    (run : Multifinger.Execution s xs t cost) :
    ∃ (after : Hand) (k : Nat), after.Represents t ∧ Pointer.Execution h.tree xs after.tree k ∧
      k + after.potential ≤ (344 + 60 * (fingers + 1)) * cost + h.potential := by
  induction run generalizing h with
  | nil => exact ⟨h, 0, rep, .nil, by simp⟩
  | cons request tail ih =>
    obtain ⟨middle, k, middleRep, first, firstCost⟩ := simulate_serves rep valid request
    obtain ⟨after, m, target, rest, restCost⟩ := ih middleRep (request.valid valid).1
    refine ⟨after, k + m, target, .cons first rest, ?_⟩
    simp only [Nat.mul_add, Nat.mul_one] at firstCost restCost ⊢
    omega

/-- All-root initialization starts in the same physical tree at zero potential.
For any fixed number of fingers this is a constant-factor conventional BST
execution, without an additive term depending on the tree size. -/
theorem one_finger_execution (fingers : Nat) (tree : Tree) (nonempty : 0 < tree.size)
    {t : Multifinger.State fingers} {xs : List Nat} {cost : Nat}
    (run : Multifinger.Execution (Multifinger.initial fingers tree) xs t cost) :
    ∃ (after : Hand) (k : Nat), after.Represents t ∧ Pointer.Execution tree xs after.tree k ∧
      k ≤ (344 + 60 * (fingers + 1)) * cost := by
  obtain ⟨after, k, target, execution, bound⟩ :=
    simulate_execution (forState_represents _) (Multifinger.initial_valid fingers tree nonempty) run
  have initial := initial_tree fingers tree
  rw [initial.1] at execution
  rw [initial.2] at bound
  exact ⟨after, k, target, execution, by omega⟩

end RotationBST.FingerHand.Hand
