module

public import RotationBST.Algorithms.GreedyASS.Combination.Deamortized.Abstract
public import RotationBST.Algorithms.Combination.Analysis.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.UniformCombination
open Combo Geometric.GreedyASS.Combination

private def leaf : Tree := .node .nil .nil

-- Empty input never triggers the shared snapshot or changes the starting tree.
example {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) : p.cost [] = 0 ∧ p.finalTree [] = saved := ⟨rfl, rfl⟩

-- The common allowance is linear and independent of Tango's log-log factor.
example : overhead leaf = 46225920 := by
  norm_num [overhead, leaf, Tree.size]

-- Choose one prepared policy before every weight assignment. On a one-key
-- universe a root request still costs one in the weighted benchmark, although
-- the legal offline comparator makes no rotations.
example (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ p : Policy leaf fields oldData,
      Pointer.Execution leaf [0] (p.finalTree [0]) (p.cost [0]) ∧
      ∀ w : Nat → ℝ, 0 < w 0 → WeightedFinger.costFrom w 0 [0] = 1 ∧
        (p.cost [0] : ℝ) ≤ 1307904 * min (184903680 * WeightedFinger.costFrom w 0 [0])
          (4 * Tango.Combination.linearChargeFactor (Tango.balanced leaf.size) : Nat) + 3839872 * overhead leaf := by
  obtain ⟨p⟩ := Results.policy_exists leaf (by decide +kernel) fields oldData
  have valid : ∀ x ∈ [0], x < leaf.size := by intro x member; simp at member; subst x; decide +kernel
  have physical := (Results.tree_bound p leaf rfl [0] valid).1
  refine ⟨p, physical, ?_⟩
  intro w positive
  have weights : ∀ x < leaf.size, 0 < w x := by
    intro x key
    have same : x = 0 := by change x < 1 at key; omega
    simpa only [same] using positive
  have comparator : Execution leaf [0] leaf 0 := .cons ⟨.refl, rfl⟩ .nil
  have bound := Results.weights_competitive p 0 (by decide +kernel) w weights rfl comparator
  refine ⟨?_, ?_⟩
  · simp only [WeightedFinger.costFrom, WeightedFinger.Results.repeated_key w 0 positive, add_zero]
  · simpa only [List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero, Nat.cast_one, mul_one] using bound

private def zeroWorker : Controller.Worker Unit := ⟨fun _ => (), fun _ _ _ => ((), true)⟩

-- The multiplier hypothesis in overhead_mono is necessary. With C1 = 0,
-- increasing a zero allowance breaks segment stability even on empty input.
example : Analysis.WellBehaved zeroWorker 0 0 1 0 (fun _ _ _ => 0) ∧
    ¬ Analysis.WellBehaved zeroWorker 0 1 1 0 (fun _ _ _ => 0) := by
  constructor
  · refine ⟨by simp, ?_, ?_, ?_⟩
    · intro side earlier state spent ran valid x key
      omega
    · intro side xs valid
      cases xs with
      | nil => exact ⟨(), 0, .nil, by simp [Analysis.total, Analysis.mass]⟩
      | cons x xs => have := valid x (by simp); omega
    · intro side xs valid lo hi ordered inside
      simp [Analysis.total, Analysis.mass]
  · intro bad
    have impossible := bad.stable false [] (by simp) 0 0 (by omega) (by simp)
    norm_num [Analysis.total, Analysis.mass] at impossible

-- One combined deamortized program handles empty input and repeated root
-- requests. The same chosen program has valid responses and a worst-case
-- bound even when its offline comparator needs no rotations.
example (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ p : Policy leaf fields oldData, ∃ d : Deamortized p,
      (∃ empty, d.program [] = some empty ∧ empty.costs = []) ∧
      ∃ out, d.program [0, 0, 0] = some out ∧ out.costs.length = 3 ∧
        (∀ cost ∈ out.costs, (cost : ℝ) < 251) ∧
        out.costs.sum = 3 + out.instructions.length := by
  obtain ⟨p, d, all⟩ := Deamortized.Results.combined leaf (by decide +kernel) fields oldData
  obtain ⟨empty, emptyRun, _emptyServed, emptyLength, _emptySum, _emptyWorst, _emptyBound⟩ := all [] (by simp)
  have valid : ∀ x ∈ [0, 0, 0], x < leaf.size := by
    intro x member
    have key : x = 0 := by simpa using member
    subst x
    decide +kernel
  obtain ⟨out, run, _served, length, total, worst, _bound⟩ := all [0, 0, 0] valid
  refine ⟨p, d, ⟨empty, emptyRun, List.eq_nil_of_length_eq_zero emptyLength⟩, out, run, length, ?_, total⟩
  simpa [leaf, Tree.size] using worst

end RotationBST.Tests.UniformCombination
