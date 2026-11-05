module

public import RotationBST.Algorithms.GreedyASS.Reference.Conversion.Distance
public import RotationBST.Algorithms.GreedyASS.Potential.Amortized.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Conversion
open Potential.Amortized

theorem with_predecessor (t : Tree) (p : Nat) (xs : List Nat)
    (hp : p < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    xs.length + edgeCost (convert t) 0 (p :: xs) ≤ 5 * LazyFinger.costFrom t p xs := by
  induction xs generalizing p with
  | nil => simp [edgeCost, LazyFinger.costFrom]
  | cons x xs ih =>
    have hx := valid x (by simp)
    have pair := distance t 0 p x hp hx
    have rest := ih x hx (fun y hy => valid y (List.mem_cons_of_mem _ hy))
    simp only [Nat.zero_add] at pair
    simp only [List.length_cons, edgeCost, LazyFinger.costFrom]
    omega

/-- A leaf-oriented reference simultaneously compares with every valid
initial finger of the original BST. Omitting its first traversal only helps. -/
theorem cost_from (t : Tree) (p : Nat) (xs : List Nat)
    (hp : p < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    referenceCost (convert t) 0 xs ≤ 5 * LazyFinger.costFrom t p xs := by
  have bound := with_predecessor t p xs hp valid
  cases xs with
  | nil => simp [referenceCost, edgeCost, LazyFinger.costFrom]
  | cons x xs =>
    simp only [referenceCost, edgeCost] at bound ⊢
    omega

theorem cost (t : Tree) (xs : List Nat) (nonempty : 0 < t.size)
    (valid : ∀ x ∈ xs, x < t.size) :
    referenceCost (convert t) 0 xs ≤ 5 * LazyFinger.cost t xs := by
  cases t with
  | nil => simp [Tree.size] at nonempty
  | node l r => exact cost_from (.node l r) l.size xs (by simp [Tree.size]; omega) valid

end RotationBST.Geometric.GreedyASS.Reference.Conversion
