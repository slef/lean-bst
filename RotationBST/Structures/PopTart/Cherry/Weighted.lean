module

public import RotationBST.Structures.PopTart.Cherry.Rank
public import RotationBST.Structures.PopTart.Cherry.Ordered
public import RotationBST.Structures.PopTart.Slots
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Cherry
open WeightedTree

/-- Lemma 3: nonincreasing fringe weights turn the rank bound into a weighted
logarithmic depth bound. Queried weights must be positive; other weights may
be zero. The additive constant handles the first-ranked leaf. -/
theorem weighted_depth {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom)
    (ordered : (layers.decode bottom).Ordered)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt (layers.decode bottom) subtree weight depth) (positive : 0 < weight) :
    (depth : ℝ) ≤ 3 + 4 * Real.logb 2 ((layers.decode bottom).mass / weight) := by
  obtain ⟨before, after, split, rankBound⟩ := depth_rank valid base slot
  have massBound := ordered_prefix_mass ordered split
  have rankRatio : ((before.length + 1 : Nat) : ℝ) ≤ (layers.decode bottom).mass / weight :=
    (le_div_iff₀ positive).mpr massBound
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) rankRatio
  linarith only [rankBound, logarithm]

/-- Weighted access reaches the actual root of a nonempty frozen fringe
subtree, with cost equal to its outer depth. -/
theorem weighted_access {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom)
    (ordered : (layers.decode bottom).Ordered)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt (layers.decode bottom) subtree weight depth) (positive : 0 < weight)
    (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.plug cs subtree = (layers.decode bottom).tree ∧
      Pointer.Trace ⟨(layers.decode bottom).tree, []⟩ ⟨subtree, cs⟩ depth ∧
      (depth : ℝ) ≤ 3 + 4 * Real.logb 2 ((layers.decode bottom).mass / weight) := by
  obtain ⟨cs, length, plugged, trace⟩ := slot_trace slot nonempty
  exact ⟨cs, length, plugged, trace, weighted_depth valid base ordered slot positive⟩

/-- Empty initialization and increasing pushes retain Lemma 3's weighted
invariant together with Lemma 2's concrete mixed-history cost guarantee. -/
theorem weighted_sequence {rest : Layers} {n : Nat} (program : Program 0 .nil rest n)
    {bottom : WeightedTree} (base : Perfect 0 bottom) (bottomNonnegative : bottom.Nonnegative)
    (increasing : program.Increasing bottom) :
    Valid 0 rest ∧ (rest.decode bottom).Ordered ∧ program.Realizes bottom ∧ n + program.cost ≤ 11 * n ∧
      ∀ subtree weight depth, SlotAt (rest.decode bottom) subtree weight depth → 0 < weight →
        (depth : ℝ) ≤ 3 + 4 * Real.logb 2 ((rest.decode bottom).mass / weight) := by
  have initial : (Layers.nil.decode bottom).Ordered := by
    cases base
    exact ⟨bottomNonnegative, by simp [Layers.decode, fringe]⟩
  have ordered := sequence_ordered program initial increasing
  obtain ⟨valid, realizes, bound⟩ := empty_sequence program bottom
  exact ⟨valid, ordered, realizes, bound, fun _ _ _ slot positive =>
    weighted_depth valid base ordered slot positive⟩

end RotationBST.PopTart.Cherry
