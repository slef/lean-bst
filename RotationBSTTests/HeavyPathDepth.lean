module

public import RotationBST.Structures.HeavyPath.Recursive.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.HeavyPathDepth
open HeavyPath HeavyPath.Paired HeavyPath.Recursive LabelledCursor

private def single (x : Nat) : LabelledTree Nat := .node .nil x .nil
private def source : LabelledTree Nat :=
  .node (.node (single 0) 1 .nil) 3 (.node (.node (single 0) 1 (single 0)) 2 .nil)
private def weight : Nat → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | _ => 8

private theorem positive : Positive weight source := by
  norm_num [source, single, Positive, weight]

private theorem sourceMass : mass weight source = 19 := by
  norm_num [source, single, mass, weight]

private theorem sourceKeys : source.inorder = [0, 1, 3, 0, 1, 0, 2] := rfl

-- The same label occurs in a lower payload, at the heavy-path endpoint,
-- and in an upper payload. All three ranks use the full theorem directly.
example : (Tree.depth (rebuild weight source) 0 : ℝ) ≤ 7 + 15 * Real.logb 2 19 := by
  have bound := Recursive.Results.rebuild_depth positive
    (before := []) (key := 0) (after := [1, 3, 0, 1, 0, 2]) sourceKeys
  simpa only [List.length_nil, sourceMass, weight, div_one] using bound

example : (Tree.depth (rebuild weight source) 3 : ℝ) ≤ 7 + 15 * Real.logb 2 19 := by
  have bound := Recursive.Results.rebuild_depth positive
    (before := [0, 1, 3]) (key := 0) (after := [1, 0, 2]) sourceKeys
  simpa only [List.length_cons, List.length_nil, sourceMass, weight, div_one] using bound

example : (Tree.depth (rebuild weight source) 5 : ℝ) ≤ 7 + 15 * Real.logb 2 19 := by
  have bound := Recursive.Results.rebuild_depth positive
    (before := [0, 1, 3, 0, 1]) (key := 0) (after := [2]) sourceKeys
  simpa only [List.length_cons, List.length_nil, sourceMass, weight, div_one] using bound

-- The nonuniform weight of a separator is its own node weight, not its
-- payload's weight or the entire frame charge.
example : (Tree.depth (rebuild weight source) 2 : ℝ) ≤ 7 + 15 * Real.logb 2 (19 / 8) := by
  have bound := Recursive.Results.rebuild_depth_at positive ⟨2, by decide⟩
  simpa only [sourceMass, sourceKeys, List.getElem_cons_succ, List.getElem_cons_zero, weight] using bound

-- Every rank is covered without a separately supplied occurrence or child bound.
example (rank : Fin 7) : (Tree.depth (rebuild (fun _ => 1) source) rank.val : ℝ) ≤
    7 + 15 * Real.logb 2 7 := by
  exact Recursive.Results.rebuild_unit_depth source rank.val rank.isLt

-- The visit reaches the requested rank and has a charged return to the same root.
example : ∃ (visited : Pointer.Config) (cost : Nat),
    visited.tree = rebuild weight source ∧ visited.key? = some 6 ∧
    Pointer.Trace ⟨rebuild weight source, []⟩ visited cost ∧
    Pointer.Trace visited ⟨rebuild weight source, []⟩ cost ∧
    (1 + 2 * cost : ℝ) ≤ 15 + 30 * Real.logb 2 (19 / 4) := by
  have walk := Recursive.Results.rebuild_search_walk positive ⟨6, by decide⟩
  simpa only [sourceMass, sourceKeys, List.getElem_cons_succ, List.getElem_cons_zero, weight] using walk

-- Empty trees admit no valid search rank; the API does not claim a phantom key.
example (rank : Fin (LabelledTree.nil : LabelledTree Nat).inorder.length) : False :=
  Fin.elim0 rank

end RotationBST.Tests.HeavyPathDepth
