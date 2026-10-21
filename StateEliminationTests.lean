import StateElimination
open RotationBST

private def leaf : Tree := .node .nil .nil
private def two : Tree := .node leaf .nil
private def three : Tree := .node .nil (.node .nil leaf)

example : moveToRoot three 2 = (.node (.node .nil leaf) .nil, 2) := by decide
example : ∃ u k, Access three u 2 k ∧ k < three.size := access_exists three 2 (by decide)
example : moveToRootAlgorithm.totalCost two [0, 0, 1, 1] = 6 := by decide

/-- Private memory can change while the tree stays unchanged. -/
private def toggling : StatefulAlgorithm Bool where
  init _ := false
  step q t x := (!q, moveToRoot t x)
  correct _ t x hx := (moveToRoot_correct t x hx).1

example : toggling.totalCost three [2, 0, 1, 2] = moveToRootAlgorithm.totalCost three [2, 0, 1, 2] :=
  by decide

/-- A private cache of tree size is exactly recoverable. -/
private def cachedSize : StatefulAlgorithm Nat where
  init := Tree.size
  step _ t x := (t.size, moveToRoot t x)
  correct _ t x hx := (moveToRoot_correct t x hx).1

private theorem cache_preserved (t : Tree) (x : Nat) (hx : x < t.size) :
    (cachedSize.step t.size t x).1 = (cachedSize.step t.size t x).2.1.size :=
  (moveToRoot_correct t x hx).1.1.size_eq

example (t : Tree) (xs : List Nat) (hv : ValidInput t xs) :
    (cachedSize.erase Tree.size).totalCost t xs = cachedSize.totalCost t xs :=
  cachedSize.erase_totalCost Tree.size (fun _ => rfl) cache_preserved t xs hv

example (t : Tree) (xs : List Nat) (hv : ValidInput t xs) :
    moveToRootAlgorithm.totalCost t xs ≤ t.size * toggling.totalCost t xs :=
  size_factor_simulation toggling t xs hv

-- Exact state recovery is sufficient, not automatic even for one private bit.
-- This does NOT refute StateElimination: toggling ignores its bit when choosing rotations.
example : ¬ ∃ recover : Tree → Bool, ∀ t x, x < t.size →
    (toggling.step (recover t) t x).1 = recover (toggling.step (recover t) t x).2.1 := by
  rintro ⟨recover, hp⟩
  have h := hp leaf 0 (by decide)
  simp [toggling, leaf, moveToRoot, Tree.size] at h

/-- info: 'RotationBST.moveToRoot_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms moveToRoot_correct
/-- info: 'RotationBST.size_factor_simulation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms size_factor_simulation
/-- info: 'RotationBST.StatefulAlgorithm.erase_totalCost' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StatefulAlgorithm.erase_totalCost
/-- info: 'RotationBST.stateElimination_of_universal' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateElimination_of_universal
