module

public import RotationBST.Structures.PopTart.Cherry.Depth
public import RotationBST.Structures.PopTart.Fringe
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Cherry
open WeightedTree

/-- A slot's layer is controlled by the number of preceding fringe occurrences.
The general-level offset lets the same induction handle carries of any size. -/
theorem rank_certificate {level : Nat} {layers : Layers} (valid : Valid level layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt (layers.decode bottom) subtree weight depth) :
    ∃ before after j, (layers.decode bottom).fringe = before ++ (subtree, weight) :: after ∧
      depth ≤ level + 4 * j + 3 ∧ 2 ^ (level + j) ≤ before.length + 2 ^ level := by
  induction valid generalizing depth with
  | nil level =>
    obtain ⟨before, after, split⟩ := slot_split slot
    have zero := perfect_depth base slot
    exact ⟨before, after, 0, split, by omega, by simp⟩
  | @one level a tail pa vt ih =>
    cases slot with
    | left found =>
      obtain ⟨before, after, split⟩ := slot_split found
      have eq := perfect_depth pa found
      refine ⟨before, after ++ (tail.decode bottom).fringe, 0, ?_, by omega, by simp⟩
      simp [Layers.decode, fringe, split, List.append_assoc]
    | right found =>
      obtain ⟨before, after, j, split, bound, population⟩ := ih found
      refine ⟨a.fringe ++ before, after, j + 1, ?_, ?_, ?_⟩
      · simp [Layers.decode, fringe, split, List.append_assoc]
      · omega
      · simp only [List.length_append, fringe_length, perfect_count pa]
        rw [show level + (j + 1) = level + 1 + j by omega]
        rw [pow_succ] at population
        omega
  | @two level a b tail pa pb vt ih =>
    cases slot with
    | left found =>
      obtain ⟨before, after, split⟩ := slot_split found
      have eq := perfect_depth pa found
      refine ⟨before, after ++ b.fringe ++ (tail.decode bottom).fringe, 0, ?_, by omega, by simp⟩
      simp [Layers.decode, fringe, split, List.append_assoc]
    | right found =>
      cases found with
      | left hit =>
        obtain ⟨before, after, split⟩ := slot_split hit
        have eq := perfect_depth pb hit
        refine ⟨a.fringe ++ before, after ++ (tail.decode bottom).fringe, 0, ?_, by omega, by simp⟩
        simp [Layers.decode, fringe, split, List.append_assoc]
      | right hit =>
        obtain ⟨before, after, j, split, bound, population⟩ := ih hit
        refine ⟨a.fringe ++ b.fringe ++ before, after, j + 1, ?_, ?_, ?_⟩
        · simp [Layers.decode, fringe, split, List.append_assoc]
        · omega
        · simp only [List.length_append, fringe_length, perfect_count pa, perfect_count pb]
          rw [show level + (j + 1) = level + 1 + j by omega]
          rw [pow_succ] at population
          omega
  | @three level a b c tail pa pb pc vt ih =>
    cases slot with
    | left found =>
      obtain ⟨before, after, split⟩ := slot_split found
      have eq := perfect_depth pa found
      refine ⟨before, after ++ b.fringe ++ c.fringe ++ (tail.decode bottom).fringe, 0, ?_, by omega, by simp⟩
      simp [Layers.decode, fringe, split, List.append_assoc]
    | right found =>
      cases found with
      | left hit =>
        obtain ⟨before, after, split⟩ := slot_split hit
        have eq := perfect_depth pb hit
        refine ⟨a.fringe ++ before, after ++ c.fringe ++ (tail.decode bottom).fringe, 0, ?_, by omega, by simp⟩
        simp [Layers.decode, fringe, split, List.append_assoc]
      | right hit =>
        cases hit with
        | left last =>
          obtain ⟨before, after, split⟩ := slot_split last
          have eq := perfect_depth pc last
          refine ⟨a.fringe ++ b.fringe ++ before, after ++ (tail.decode bottom).fringe, 0, ?_, by omega, by simp⟩
          simp [Layers.decode, fringe, split, List.append_assoc]
        | right last =>
          obtain ⟨before, after, j, split, bound, population⟩ := ih last
          refine ⟨a.fringe ++ b.fringe ++ c.fringe ++ before, after, j + 1, ?_, ?_, ?_⟩
          · simp [Layers.decode, fringe, split, List.append_assoc]
          · omega
          · simp only [List.length_append, fringe_length, perfect_count pa, perfect_count pb, perfect_count pc]
            rw [show level + (j + 1) = level + 1 + j by omega]
            rw [pow_succ] at population
            omega

/-- The kth occurrence, counting from one, has depth at most `3 + 4 log₂ k`.
The additive constant covers even the first leaf of a nonempty stack. -/
theorem depth_rank {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt (layers.decode bottom) subtree weight depth) :
    ∃ before after, (layers.decode bottom).fringe = before ++ (subtree, weight) :: after ∧
      (depth : ℝ) ≤ 3 + 4 * Real.logb 2 ((before.length + 1 : Nat) : ℝ) := by
  obtain ⟨before, after, j, split, bound, population⟩ := rank_certificate valid base slot
  have natural : 2 ^ j ≤ before.length + 1 := by simpa using population
  have realPopulation : (2 : ℝ) ^ j ≤ ((before.length + 1 : Nat) : ℝ) := by exact_mod_cast natural
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) realPopulation
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at logarithm
  have realBound : (depth : ℝ) ≤ 4 * (j : ℝ) + 3 := by
    exact_mod_cast (by simpa only [Nat.zero_add] using bound)
  exact ⟨before, after, split, by linarith only [realBound, logarithm]⟩

end RotationBST.PopTart.Cherry
