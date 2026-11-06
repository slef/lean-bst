module

public import RotationBST.Algorithms.GreedyASS.Combination.Definitions.Abstract
public import RotationBST.Algorithms.Deamortization.Scheduler.Definitions.Abstract

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Combination

/-- A fixed physical program with exact per-request costs. Setup is paid once,
before the sequence. Its choices precede all weights and offline comparators.
The simulation bounds abstract BST instructions, not private computation. -/
structure Deamortized {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) where
  initial : Tree
  startup : Nat
  program : List Nat → Option Deamortization.Scheduler.Output
  setup : Pointer.Trace ⟨saved, []⟩ ⟨initial, []⟩ startup
  setup_bound : startup ≤ 16 * saved.size
  correct : ∀ keys, (∀ x ∈ keys, x < saved.size) →
    ∃ out, program keys = some out ∧
      Multifinger.replay out.instructions ⟨initial, []⟩ = some out.state.cursor ∧
      Deamortization.Scheduler.ServedStream ⟨initial, []⟩ keys out.state.cursor out.instructions out.costs ∧
      Multifinger.Execution (Deamortization.Scheduler.cursorState ⟨initial, []⟩) keys
        (Deamortization.Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
      out.costs.length = keys.length ∧ out.costs.sum = keys.length + out.instructions.length ∧
      out.costs.sum ≤ 2480 * p.cost keys ∧
      ∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 saved.size
  causal : ∀ xs ys out, program (xs ++ ys) = some out →
    ∃ first, program xs = some first ∧ first.instructions <+: out.instructions ∧
      first.costs <+: out.costs

end RotationBST.Geometric.GreedyASS.Combination
