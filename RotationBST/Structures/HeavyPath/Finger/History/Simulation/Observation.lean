module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Execution

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation
open LabelledCursor

/-- At every certified prefix, the physical root is the source finger. -/
theorem root_key {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) :
    (Pointer.Config.mk s.pair.tree []).key? = c.erase.key? := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => exact False.elim valid
  | node l key r => exact History.Results.state_root_key valid

/-- The bounded-depth guarantee is available after every policy prefix, for
every key occurrence, including nonuniform positive weights. -/
theorem depth {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) (rank : Fin c.tree.inorder.length) :
    (Tree.depth s.pair.tree rank.val : ℝ) ≤
      15 + 15 * Real.logb 2 (HeavyPath.mass weight c.tree /
        weight (c.tree.inorder[rank.val]'rank.isLt)) := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => exact False.elim valid
  | node l key r => exact History.Results.state_depth_at valid rank

/-- A checked search and return is available at every certified prefix. -/
theorem search_walk {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) (rank : Fin c.tree.inorder.length) :
    ∃ (visited : Pointer.Config) (cost : Nat),
      visited.tree = s.pair.tree ∧ visited.key? = some rank.val ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ visited cost ∧
      Pointer.Trace visited ⟨s.pair.tree, []⟩ cost ∧
      (1 + 2 * cost : ℝ) ≤ 31 + 30 * Real.logb 2
        (HeavyPath.mass weight c.tree / weight (c.tree.inorder[rank.val]'rank.isLt)) := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => exact False.elim valid
  | node l key r => exact History.Results.state_search_walk valid rank

end RotationBST.HeavyPath.Finger.History.Simulation
