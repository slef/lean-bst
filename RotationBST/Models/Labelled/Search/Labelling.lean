module

public import RotationBST.Models.Labelled.Search.Definitions.Abstract
public import RotationBST.Models.Labelled.Ordering
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tree

theorem labelWith_erase (t : Tree) (keys : List Nat) : (t.labelWith keys).erase = t := by
  induction t generalizing keys with
  | nil => rfl
  | node l r il ir => simp only [labelWith, LabelledTree.erase, il, ir]

/-- The executable labelling construction preserves every sparse key in order. -/
theorem labelWith_inorder (t : Tree) (keys : List Nat) (same : keys.length = t.size) :
    (t.labelWith keys).inorder = keys := by
  induction t generalizing keys with
  | nil =>
    have empty : keys = [] := List.eq_nil_of_length_eq_zero same
    exact empty.symm
  | node l r il ir =>
    have index : l.size < keys.length := by simp only [Tree.size] at same; omega
    have leftLength : (keys.take l.size).length = l.size := by simp only [List.length_take]; omega
    have rightLength : (keys.drop (l.size + 1)).length = r.size := by
      simp only [List.length_drop, Tree.size] at *; omega
    simp only [labelWith, LabelledTree.inorder, il _ leftLength, ir _ rightLength,
      List.getElem?_eq_getElem index, Option.getD_some]
    rw [← List.drop_eq_getElem_cons index, List.take_append_drop]

theorem labelWith_ordered (t : Tree) (keys : List Nat) (same : keys.length = t.size)
    (ordered : keys.Pairwise (· < ·)) : (t.labelWith keys).Ordered := by
  rw [Representation.OrderingBridge.ordered_iff, labelWith_inorder t keys same]
  exact ordered

end RotationBST.Tree
