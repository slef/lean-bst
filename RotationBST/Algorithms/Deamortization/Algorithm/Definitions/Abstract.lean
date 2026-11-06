module

public import RotationBST.Models.Online.Abstract
public import RotationBST.Algorithms.Deamortization.Scheduler.Definitions.Abstract
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section
namespace RotationBST.Deamortization.Algorithm

/-- One causal deamortized physical program for a rotation-model algorithm.
The source and saved tree are fixed before requests and cost benchmarks.
Setup is a separate linear trace; computation and storage are abstract. -/
structure Implementation (source : RotationBST.Algorithm) (saved : Tree) where
  initial : Tree
  startup : Nat
  program : List Nat → Option Scheduler.Output
  setup : Pointer.Trace ⟨saved, []⟩ ⟨initial, []⟩ startup
  setup_bound : startup ≤ 16 * saved.size
  correct : ∀ keys, (∀ x ∈ keys, x < saved.size) →
    ∃ out, program keys = some out ∧
      Multifinger.replay out.instructions ⟨initial, []⟩ = some out.state.cursor ∧
      Scheduler.ServedStream ⟨initial, []⟩ keys out.state.cursor out.instructions out.costs ∧
      Multifinger.Execution (Scheduler.cursorState ⟨initial, []⟩) keys
        (Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
      out.costs.length = keys.length ∧ out.costs.sum = keys.length + out.instructions.length ∧
      out.costs.sum ≤ 79360 * source.totalCost saved keys ∧
      ∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 saved.size
  causal : ∀ xs ys out, program (xs ++ ys) = some out →
    ∃ first, program xs = some first ∧ first.instructions <+: out.instructions ∧
      first.costs <+: out.costs

end RotationBST.Deamortization.Algorithm
