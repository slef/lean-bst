module

public import RotationBST.Structures.HeavyPath.Finger.Transfer.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Down
open PopTart PopTart.WeightedTree PopTart.Chocolate

theorem downLeft_fringe {p : Pair} (valid : p.Valid) {old a b : Tree} {oldCharge : ℝ}
    (exposed : p.lower.top = .leaf old.mirror oldCharge)
    (lowerCharge : ℝ) {upperCharge : ℝ} (upperNonnegative : 0 ≤ upperCharge) :
    ∃ before,
      p.lower.decode.mirror.fringe = before ++ [(old, oldCharge)] ∧
      (p.downLeft a b lowerCharge upperCharge).lower.decode.mirror.fringe = before ++ [(a, lowerCharge)] ∧
      (p.downLeft a b lowerCharge upperCharge).upper.decode.fringe = (b, upperCharge) :: p.upper.decode.fringe := by
  have upper := (Chocolate.Results.push valid.2 (.leaf b upperCharge) upperNonnegative []).2.1
  cases tail : p.lower.topTail with
  | none =>
    refine ⟨[], ?_, ?_, upper⟩
    · rw [decode_top p.lower, tail, exposed]
      simp only [Option.elim, WeightedTree.mirror, WeightedTree.fringe, Tree.mirror_mirror, List.nil_append]
    · change (p.lower.replaceTop (.leaf a.mirror lowerCharge)).decode.mirror.fringe = _
      rw [replaceTop_decode, tail]
      simp only [Option.elim, WeightedTree.mirror, WeightedTree.fringe, Tree.mirror_mirror, List.nil_append]
  | some suffix =>
    refine ⟨suffix.mirror.fringe, ?_, ?_, upper⟩
    · rw [decode_top p.lower, tail, exposed]
      simp only [Option.elim, WeightedTree.mirror, WeightedTree.fringe, Tree.mirror_mirror]
    · change (p.lower.replaceTop (.leaf a.mirror lowerCharge)).decode.mirror.fringe = _
      rw [replaceTop_decode, tail]
      simp only [Option.elim, WeightedTree.mirror, WeightedTree.fringe, Tree.mirror_mirror]

theorem downRight_fringe {p : Pair} (valid : p.Valid) {old a b : Tree} {oldCharge : ℝ}
    (exposed : p.upper.top = .leaf old oldCharge)
    {lowerCharge : ℝ} (upperCharge : ℝ) (lowerNonnegative : 0 ≤ lowerCharge) :
    ∃ after,
      p.upper.decode.fringe = (old, oldCharge) :: after ∧
      (p.downRight a b lowerCharge upperCharge).upper.decode.fringe = (b, upperCharge) :: after ∧
      (p.downRight a b lowerCharge upperCharge).lower.decode.mirror.fringe =
        p.lower.decode.mirror.fringe ++ [(a, lowerCharge)] := by
  have pushed := (Chocolate.Results.push valid.1 (.leaf a.mirror lowerCharge) lowerNonnegative []).2.1
  have lower : (p.downRight a b lowerCharge upperCharge).lower.decode.mirror.fringe =
      p.lower.decode.mirror.fringe ++ [(a, lowerCharge)] := by
    change (p.lower.push (.leaf a.mirror lowerCharge)).decode.mirror.fringe = _
    rw [mirror_fringe, pushed, mirror_fringe]
    simp only [WeightedTree.fringe, List.singleton_append, List.map_cons, List.reverse_cons, Tree.mirror_mirror]
  cases tail : p.upper.topTail with
  | none =>
    refine ⟨[], ?_, ?_, lower⟩
    · rw [decode_top p.upper, tail, exposed]
      rfl
    · change (p.upper.replaceTop (.leaf b.mirror.mirror upperCharge)).decode.fringe = _
      rw [replaceTop_decode, tail, Tree.mirror_mirror]
      rfl
  | some suffix =>
    refine ⟨suffix.fringe, ?_, ?_, lower⟩
    · rw [decode_top p.upper, tail, exposed]
      rfl
    · change (p.upper.replaceTop (.leaf b.mirror.mirror upperCharge)).decode.fringe = _
      rw [replaceTop_decode, tail, Tree.mirror_mirror]
      rfl

end RotationBST.HeavyPath.Finger.History.Down
