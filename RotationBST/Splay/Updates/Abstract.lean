module

import RotationBST.AbstractAudit.Check
public import RotationBST.Splay.Updates.AbstractBridge

@[expose] public section

/-! Standard updates: see `Updates/Algorithm/Abstract` for the four small
executable definitions, and `Updates/Execution/Abstract` for the costed forest
machine. Splits and joins use local inorder ranks; inserting or deleting a key
renumbers subsequent ranks. The potential analysis remains entirely on shapes. -/
namespace RotationBST.Splay.Updates.Results

variable {s t : List Tree} {N m c : Nat} {ns : List Nat}

theorem split_sizes (t : Tree) (k : Nat) (valid : k ≤ t.size) :
    (split t k).left.size = k ∧ (split t k).right.size = t.size - k :=
  Updates.split_sizes t k valid

/-- A nontrivial split consists of a certified predecessor access and one cut. -/
theorem split_spec (t : Tree) (k : Nat) (valid : k ≤ t.size) (positive : 0 < k) :
    ∃ l r c, Access t (.node l r) (k - 1) c ∧ split t k = ⟨.node l .nil, r, c⟩ :=
  Updates.split_spec t k valid positive

theorem join_size (l r : Tree) : (join l r).1.size = l.size + r.size :=
  Updates.join_size l r

theorem insert_size (t : Tree) (k : Nat) (valid : k ≤ t.size) :
    (insert t k).1.size = t.size + 1 :=
  Updates.insert_size t k valid

theorem delete_size (t : Tree) (x : Nat) (valid : x < t.size) :
    (delete t x).1.size = t.size - 1 :=
  Updates.delete_size t x valid

/-- Balance theorem with access, insertion, deletion, split, and join.
At most `N` keys are stored across the forest; `m` is the number of operations.
Cost `c` includes one unit per operation and every splay rotation. -/
theorem balance (execution : Execution N s m t c) :
    (c : ℝ) ≤ (m : ℝ) * (5 * Real.logb 2 (N + 1 : Nat) + 3) +
      (forestSize s : ℝ) * Real.logb 2 (forestSize s + 1 : Nat) :=
  Updates.balance execution

/-- Sharper, operation-sensitive bound, exactly for initially empty trees.
The list `ns` records only the keys involved in each operation, not the entire forest. -/
theorem balance_initially_empty (execution : LocalExecution s ns t c) (empty : forestSize s = 0) :
    (c : ℝ) ≤ (ns.map fun n : Nat => 5 * Real.logb 2 (n + 1 : Nat) + 3).sum :=
  Updates.balance_initially_empty execution empty

end RotationBST.Splay.Updates.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
#check_bst_abstract RotationBST.Splay.Updates.Results allowing [
  RotationBST.Model.Abstract,
  RotationBST.Online.Abstract,
  RotationBST.Pointer.Machine.Abstract,
  RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Updates.Algorithm.Abstract,
  RotationBST.Splay.Updates.Execution.Abstract]
