module

public import RotationBST.Structures.BSTDeque.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.BSTDeque.Deque

/-- An arbitrary maintained deque stores at most 32 units of potential per
active node, including states whose stacks have become highly unbalanced. -/
theorem potential_le_size (q : Deque) : q.potential ≤ 32 * q.size := by
  cases q with
  | empty => simp [potential, size]
  | node front a b back => simp only [potential, size, Nat.dist]; omega

end RotationBST.BSTDeque.Deque
