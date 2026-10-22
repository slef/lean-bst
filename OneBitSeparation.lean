import ThreeKeySeparation

/-! The three-key additive separation needs only one bit of private state.
The parity bit and current tree identify the appropriate serving action. -/
namespace RotationBST.ThreeKey.OneBit

/-- The current shape supplies the within-block information; the bit separates
which block is beginning at the common shape c. All other inputs use a fallback. -/
def planIndex (q : Fin 2) (t : Tree) (x : Nat) : Fin 8 :=
  if q.val = 0 then
    if t = Shape.c.tree then 0 else if t = Shape.e.tree then 2 else 4
  else
    if t = Shape.a.tree then 1 else if t = Shape.c.tree then 3 else if x = 0 then 5 else 7

def algorithm : StatefulAlgorithm (Fin 2) where
  init _ := 0
  step q t x :=
    let i := planIndex q t x
    if t = (plan i).source.tree ∧ x = (plan i).request then
      (⟨(q.val+1)%2, Nat.mod_lt _ (by decide)⟩, (plan i).target.tree, (plan i).rotations)
    else (0, moveToRoot t x)
  correct q t x hx := by
    dsimp only
    split
    next h =>
      have hp := plan_correct (planIndex q t x)
      rw [← h.1, ← h.2] at hp
      exact hp
    next => exact (moveToRoot_correct t x hx).1

theorem one_bit_period : algorithm.runFrom 0 Shape.c.tree period =
    (0, Shape.c.tree, 11) := by decide

theorem one_bit_repetitions (m : Nat) :
    algorithm.runFrom 0 Shape.c.tree (repetitions m) = (0, Shape.c.tree, 11 * m) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [repetitions, run_append, one_bit_period, ih, Nat.mul_succ, Nat.add_comm]

theorem one_bit_cost (m : Nat) : algorithm.totalCost Shape.c.tree (repetitions m) = 19 * m := by
  unfold StatefulAlgorithm.totalCost
  change (repetitions m).length + (algorithm.runFrom 0 Shape.c.tree (repetitions m)).2.2 = _
  rw [repetitions_length, one_bit_repetitions]
  dsimp only
  omega

/-- No sequence-length-independent additive allowance suffices at factor one.
The SAME online stateful algorithm and repeated word defeat EVERY tree-only rule. -/
theorem no_purely_additive_simulation (b : TreeAlgorithm) (f : Nat → Nat) :
    ∃ t xs, ValidInput t xs ∧
      algorithm.totalCost t xs + f t.size < b.totalCost t xs := by
  let m := f 3 + 1
  refine ⟨Shape.c.tree, repetitions m, ?_, ?_⟩
  · intro x hx
    rw [shape_size]
    exact repetitions_valid m x hx
  · have hl := tree_only_lower b m
    rw [one_bit_cost, shape_size]
    dsimp [m] at *
    omega

/-- The same one-bit example rules out every rational coefficient below 20/19,
even with an arbitrary additive allowance. Scaling avoids a real-number library. -/
theorem no_ratio_below_20_19 (b : TreeAlgorithm) (f : Nat → Nat)
    (numerator denominator : Nat) (hgap : 19*numerator < 20*denominator) :
    ∃ t xs, ValidInput t xs ∧
      numerator * algorithm.totalCost t xs + f t.size <
        denominator * b.totalCost t xs := by
  let m := f 3 + 1
  refine ⟨Shape.c.tree,repetitions m,?_,?_⟩
  · intro x hx
    rw [shape_size]
    exact repetitions_valid m x hx
  · have hl := Nat.mul_le_mul_left denominator (tree_only_lower b m)
    have hg : 19*numerator+1 ≤ 20*denominator := by omega
    have hm := Nat.mul_le_mul_right m hg
    rw [Nat.add_mul,Nat.one_mul] at hm
    rw [one_bit_cost,shape_size]
    have he1 : denominator*(20*m) = (20*denominator)*m := by
      rw [← Nat.mul_assoc,Nat.mul_comm denominator 20]
    have he2 : numerator*(19*m) = (19*numerator)*m := by
      rw [← Nat.mul_assoc,Nat.mul_comm numerator 19]
    rw [he1] at hl
    rw [he2]
    dsimp [m] at *
    omega


/-- info: 'RotationBST.ThreeKey.OneBit.no_purely_additive_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_purely_additive_simulation
end RotationBST.ThreeKey.OneBit
