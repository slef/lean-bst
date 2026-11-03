module

public import RotationBST.Algorithms.Tango.State.Abstract
public import RotationBST.Algorithms.Tango.Preferences.Updates.Abstract

@[expose] public section
namespace RotationBST.Tango

/-- An online marked-BST policy. A step sees only the current state, the past,
and the current request, and implements the preference-update/access bound. -/
structure Policy (reference : Tree) where
  step : List Nat → MarkedTree → Nat → MarkedTree × Nat
  correct : ∀ past s x, MarkedTree.Maintains s reference past →
    (∀ y ∈ past, y < reference.size) → x < reference.size →
    Access s.tree (step past s x).1.tree x (step past s x).2 ∧
      MarkedTree.Maintains (step past s x).1 reference (past ++ [x]) ∧
      ((step past s x).2 : ℝ) + (step past s x).1.potential - s.potential ≤
        (preferenceUpdates reference 0 past x).length * (14 * Real.logb 2 (height reference) + 4) +
          (3 * Real.logb 2 (height reference) + 1)

/-- Execute an online policy, retaining marks as the data structure's state. -/
def Policy.runFrom {reference : Tree} (policy : Policy reference) (past : List Nat)
    (s : MarkedTree) : List Nat → MarkedTree × Nat
  | [] => (s, 0)
  | x :: xs =>
      let (t, a) := policy.step past s x
      let (u, b) := policy.runFrom (past ++ [x]) t xs
      (u, a + b)

/-- Start with singleton preferred paths on the fixed reference tree. -/
def Policy.run {reference : Tree} (policy : Policy reference) (xs : List Nat) : MarkedTree × Nat :=
  policy.runFrom [] (MarkedTree.initial reference) xs

end RotationBST.Tango
