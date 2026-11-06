module

public import RotationBST.Bounds.StaticTree.Trace.Invariant
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate.Interruption
open StaticTree
open _root_.RotationBST.Tree (depth)

theorem right_bound (a s t : Tree) (constant : Nat)
    (bound : ∀ x, depth t x ≤ 4 * depth s x + (constant + 3)) :
    ∀ x, depth (.node a t) x ≤ 4 * depth (.node a s) x + constant := by
  intro x
  have localBound := bound (x - a.size - 1)
  simp only [depth]
  split_ifs <;> omega


theorem left_bound (s t b : Tree) (constant : Nat) (size : t.size = s.size)
    (bound : ∀ x, depth t x ≤ 4 * depth s x + (constant + 3)) :
    ∀ x, depth (.node t b) x ≤ 4 * depth (.node s b) x + constant := by
  intro x
  have localBound := bound x
  simp only [depth, size]
  split_ifs <;> omega

/-- Borrowing recurses two edges below the root. Their depth allowance absorbs
all six instructions of the subsequent local thaw, without a population term. -/
theorem borrow_depth (a child icing t : Tree) (size : t.size = child.size)
    (bound : ∀ x, depth t x ≤ 4 * depth child x + 8) :
    ∀ x, depth (.node a (.node t icing)) x ≤ 4 * depth (.node a (.node child icing)) x + 2 := by
  apply right_bound
  exact left_bound child t icing 5 size bound

/-- A local size-preserving repair lifts through arbitrary untouched context
without changing the multiplicative depth bound. -/
theorem context_depth (cs : List Pointer.Frame) {s t : Tree} (size : t.size = s.size)
    (bound : ∀ x, depth t x ≤ 4 * depth s x + 8) :
    ∀ x, depth (Pointer.plug cs t) x ≤ 4 * depth (Pointer.plug cs s) x + 8 := by
  induction cs generalizing s t with
  | nil => exact bound
  | cons frame cs ih =>
    cases frame with
    | left b =>
      apply ih (by simp only [Tree.size, size])
      exact left_bound s t b 8 size (fun x => (bound x).trans (by omega))
    | right a =>
      apply ih (by simp only [Tree.size, size])
      exact right_bound a s t 8 (fun x => (bound x).trans (by omega))

end RotationBST.PopTart.Chocolate.Interruption
