module

public import RotationBST.Tango.Paths.Abstract
public import RotationBST.Representation.AbstractBridge
import Mathlib.Data.List.Perm.Basic

@[expose] public section
namespace RotationBST.Tango

@[simp] theorem parts_flatten (d : PathDecomposition) : d.parts.flatten = d.1 ++ d.2.flatten := by
  rcases d with ⟨head, rest⟩
  cases head <;> simp [PathDecomposition.parts]

private theorem decompose_count (reference : Tree) (lo : Nat) (past : List Nat) (x : Nat) :
    ((decomposePaths reference lo past).1 ++ (decomposePaths reference lo past).2.flatten).count x =
      (reference.labelFrom lo).inorder.count x := by
  induction reference generalizing lo with
  | nil => rfl
  | node l r il ir =>
    have hl := il lo
    have hr := ir (lo + l.size + 1)
    cases h : (labels lo (lo + l.size) (lo + l.size + 1 + r.size) past).getLast?
    all_goals try cases ‹Bool›
    all_goals
      simp only [decomposePaths, h, Tree.labelFrom, LabelledTree.inorder,
        List.flatten_append, parts_flatten, List.count_append, List.count_cons,
        List.count_nil] at *
      omega

/-- Every reference key occurs on exactly one preferred path. -/
theorem preferredPaths_partition (reference : Tree) (past : List Nat) :
    (preferredPaths reference past).flatten.Perm (List.range reference.size) := by
  apply List.perm_iff_count.mpr
  intro x
  have h := decompose_count reference 0 past x
  simpa only [preferredPaths, parts_flatten, Representation.Bridge.inorder_label,
    List.range_eq_range'] using h

end RotationBST.Tango
