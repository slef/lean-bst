module

public import RotationBST.Classical.Scapegoat.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.Scapegoat
open Classical.Scapegoat Dictionary

private def three : List Op := [.insert 0, .insert 1, .insert 2]

-- Plain operations.
example : insertLeaf (.node .nil .nil) 1 = .node .nil (.node .nil .nil) := by decide
example : bstDelete (.node (.node .nil .nil) (.node .nil .nil)) 1 = .node (.node .nil .nil) .nil ∧
    deleteTarget (.node (.node .nil .nil) (.node .nil .nil)) 1 = 2 := by decide

-- Three increasing insertions with α = 2/3: the third leaf is at depth 2 and
-- `(2/3)² · 3 ≥ 1`, so nothing is rebuilt; costs are 1, 2 and 3.
example : (run (2 / 3) (.nil, 0) three).2 = 6 ∧
    (run (2 / 3) (.nil, 0) three).1 = (.node .nil (.node .nil (.node .nil .nil)), 3) := by
  decide +kernel
-- A fourth key at depth 3 is not too deep (`(2/3)³ · 4 ≥ 1`), a fifth at
-- depth 4 is (`(2/3)⁴ · 5 < 1`), and the whole path is then its scapegoat.
example : ¬ Violates (2 / 3) (insertLeaf (.node .nil (.node .nil (.node .nil .nil))) 3) 3 := by
  norm_num [Violates, insertLeaf, Tree.depth, Tree.size]
example : Violates (2 / 3)
    (insertLeaf (.node .nil (.node .nil (.node .nil (.node .nil .nil)))) 4) 4 := by
  norm_num [Violates, insertLeaf, Tree.depth, Tree.size]

example : Op.ValidSeq 0 (three ++ [.delete 1, .access 0]) := by
  simp [three, Op.ValidSeq, Op.Valid, Op.resize]

-- The theorems for `α = 2/3`.
example (ops : List Op) (v : Op.ValidSeq 0 ops) :
    ((run (2 / 3) (.nil, 0) ops).2 : ℝ) ≤ ops.length * bound (2 / 3) ops.length :=
  Results.total_cost_le (2 / 3) (by norm_num) ops v
example (ops : List Op) (v : Op.ValidSeq 0 ops) (z : Nat) (hz : z < (run (2 / 3) (.nil, 0) ops).1.1.size) :
    ((run (2 / 3) (.nil, 0) ops).1.1.depth z : ℝ) ≤
      Real.logb (1 / (2 / 3 : ℚ)) (run (2 / 3) (.nil, 0) ops).1.1.size + 1 :=
  Results.reachable_depth (2 / 3) (by norm_num) ops v z hz
example : Dictionary.Execution Tree.nil.unit three (run (2 / 3) (.nil, 0) three).1.1.unit
    (run (2 / 3) (.nil, 0) three).2 0 :=
  Results.run_execution (2 / 3) (.nil, 0) three (by simp [three, Op.ValidSeq, Op.Valid, Op.resize, Tree.size])

end RotationBST.Tests.Scapegoat
