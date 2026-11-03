module

public import RotationBST.Algorithms.Splay.Potential.Abstract
public import RotationBST.Algorithms.Splay.Algorithm.Abstract

@[expose] public section

/-! Conditional splaying (Sleator--Tarjan Section 5). Unlike root-access splay,
short searches leave the tree unchanged. The count below measures restructuring
rotations only; ordinary pointer searches still pay for their search paths. -/
namespace RotationBST.Splay

/-- Splay only paths at least twice the access lemma's amortized charge.
The fixed positive weights belong to this variant's decision rule. -/
noncomputable def conditionalStep (w : Nat → ℝ) (t : Tree) (x : Nat) : Tree × Nat := by
  classical
  exact if 6 * (Real.logb 2 (mass w t 0) - Real.logb 2 (w x)) + 2 ≤ (run t x).2
    then run t x else (t, 0)

/-- Execute conditional searches and accumulate only their restructuring cost. -/
noncomputable def conditionalRun (w : Nat → ℝ) : Tree → List Nat → Tree × Nat
  | t, [] => (t, 0)
  | t, x :: xs =>
      let (u, k) := conditionalStep w t x
      let (v, m) := conditionalRun w u xs
      (v, k + m)

end RotationBST.Splay
