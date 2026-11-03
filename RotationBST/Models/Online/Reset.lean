module

public import RotationBST.Models.Online.Abstract
public import RotationBST.Models.Rotation.Connectivity.Proofs

/-! An online algorithm designed for one fixed initial tree works from every
tree of the same size: on the first request, rotate into the fixed tree (at most
`2n` rotations), then run the algorithm unchanged. -/

@[expose] public section
namespace RotationBST

noncomputable def resetCost (source target : Tree) (size : source.size = target.size) : Nat :=
  Classical.choose (reset_linear source target size)

theorem resetCost_spec (source target : Tree) (size : source.size = target.size) :
    resetCost source target size ≤ 2 * source.size ∧
      Rotations source target (resetCost source target size) :=
  Classical.choose_spec (reset_linear source target size)

/-- Convert to a fixed reference shape on the first request only; afterwards
use the same online policy and its unchanged request-prefix decisions. -/
noncomputable def resetAlgorithm (algorithm : Algorithm) (reference : Tree) : Algorithm where
  step past tree request :=
    if start : past = [] ∧ tree.size = reference.size then
      let result := algorithm.step [] reference request
      (result.1, resetCost tree reference start.2 + result.2)
    else algorithm.step past tree request
  correct past tree request bound := by
    dsimp only
    split
    · rename_i start
      have access := algorithm.correct [] reference request (by omega)
      exact ⟨(resetCost_spec tree reference start.2).2.append access.1, access.2⟩
    · exact algorithm.correct past tree request bound

theorem resetAlgorithm_runFrom (algorithm : Algorithm) (reference tree : Tree)
    (past xs : List Nat) (started : past ≠ []) :
    (resetAlgorithm algorithm reference).runFrom past tree xs = algorithm.runFrom past tree xs := by
  induction xs generalizing past tree with
  | nil => rfl
  | cons request rest ih =>
    have step : (resetAlgorithm algorithm reference).step past tree request = algorithm.step past tree request := by
      simp [resetAlgorithm, started]
    simp only [Algorithm.runFrom, step]
    rw [ih _ _ (by simp)]

theorem resetAlgorithm_cost (algorithm : Algorithm) (reference tree : Tree)
    (size : tree.size = reference.size) (xs : List Nat) :
    (resetAlgorithm algorithm reference).cost tree xs ≤ algorithm.cost reference xs + 2 * tree.size := by
  cases xs with
  | nil => simp [Algorithm.cost, Algorithm.runFrom]
  | cons request rest =>
    have step : (resetAlgorithm algorithm reference).step [] tree request =
        ((algorithm.step [] reference request).1,
          resetCost tree reference size + (algorithm.step [] reference request).2) := by
      simp [resetAlgorithm, size]
    simp only [Algorithm.cost, Algorithm.runFrom, step, List.nil_append]
    rw [resetAlgorithm_runFrom algorithm reference _ [request] rest (by simp)]
    have bound := (resetCost_spec tree reference size).1
    change resetCost tree reference size + (algorithm.step [] reference request).2 +
      (algorithm.runFrom [request] (algorithm.step [] reference request).1 rest).2 ≤
      (algorithm.step [] reference request).2 +
      (algorithm.runFrom [request] (algorithm.step [] reference request).1 rest).2 + 2 * tree.size
    omega

end RotationBST
