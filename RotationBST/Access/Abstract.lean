module

public import RotationBST.Access.AbstractBridge

@[expose] public section

/-! # Accesses are precisely requests for existing keys

The elementary access and execution definitions are in `Model/Abstract.lean`.
The existence proofs are constructive, using the move-to-root baseline.
-/
namespace RotationBST

/-- Every existing key can be brought to the root in fewer than `size` rotations;
no nonexistent key can be served. This includes the empty-tree case. -/
theorem access_exists_iff (t : Tree) (x : Nat) :
    (∃ u k, Access t u x k ∧ k < t.size) ↔ x < t.size :=
  AccessBridge.exists_iff t x

/-- A request sequence is executable exactly when all its keys exist initially. -/
theorem execution_exists_iff (t : Tree) (xs : List Nat) :
    (∃ u k, Execution t xs u k) ↔ ∀ x ∈ xs, x < t.size :=
  AccessBridge.execution_iff t xs

/-- The online interface really produces legal executions on valid inputs. -/
theorem Algorithm.execution (a : Algorithm) (past : List Nat) (t : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < t.size) :
    Execution t xs (a.runFrom past t xs).1 (a.runFrom past t xs).2 :=
  AccessBridge.run_execution a past t xs valid

end RotationBST
