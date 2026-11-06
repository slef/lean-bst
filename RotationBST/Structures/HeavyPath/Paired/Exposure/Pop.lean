module

public import RotationBST.Structures.HeavyPath.Paired.Exposure.Representation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired.Exposure
open PopTart PopTart.Chocolate LabelledCursor

/-- Remove the original root frame, regardless of the stack's repair history.
The result represents the remaining solid path and is placed below the
exposed source root by an actual pointer trace. -/
theorem expose_frame {α : Type} {weight : α → ℝ} {payload : LabelledTree α → Tree}
    {cs : List (Frame α)} {frame : Frame α} {p : Stacks}
    (represented : p.Represents weight payload (cs ++ [frame])) :
    ∃ rest : Stacks, rest.Represents weight payload cs ∧
      Pointer.Trace ⟨p.tree, []⟩ ⟨Pointer.plug [replaceFrame payload frame] rest.tree, []⟩
        (p.exposeCost frame) ∧
      p.exposeCost frame + rest.potential ≤ 24 + p.potential ∧
      p.mass = rest.mass + frameMass weight frame := by
  cases frame with
  | right l x =>
    have lower : p.lower.decode.fringe =
        (payload l, mass weight l + weight x) ::
          ((lowerSlotsWith weight payload cs).reverse ++ [(.nil, 0)]) := by
      simpa [lowerSlots_append, lowerSlotsWith] using represented.2.1
    obtain ⟨rest, popped, valid, fringe, mass, bound⟩ :=
      Chocolate.Top.Results.pop_front represented.1.1 lower (by simp)
    refine ⟨⟨rest, p.upper⟩, ⟨⟨valid, represented.1.2⟩, fringe, ?_⟩, ?_, ?_, ?_⟩
    · simpa [upperSlots_append, upperSlotsWith] using represented.2.2
    · exact lower_trace popped
    · change p.lower.popCost + 4 + (rest.potential + p.upper.potential) ≤
        24 + (p.lower.potential + p.upper.potential)
      omega
    · change p.lower.decode.mass + p.upper.decode.mass =
        rest.decode.mass + p.upper.decode.mass + (HeavyPath.mass weight l + weight x)
      linarith
  | left x r =>
    have upper : p.upper.decode.fringe =
        ((payload r).mirror, weight x + mass weight r) ::
          ((upperSlotsWith weight (fun t => (payload t).mirror) cs).reverse ++ [(.nil, 0)]) := by
      simpa [upperSlots_append, upperSlotsWith] using represented.2.2
    obtain ⟨rest, popped, valid, fringe, mass, bound⟩ :=
      Chocolate.Top.Results.pop_front represented.1.2 upper (by simp)
    refine ⟨⟨p.lower, rest⟩, ⟨⟨represented.1.1, valid⟩, ?_, fringe⟩, ?_, ?_, ?_⟩
    · simpa [lowerSlots_append, lowerSlotsWith] using represented.2.1
    · simpa only [WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree,
        Tree.mirror_mirror, replaceFrame, Pointer.plug, Stacks.exposeCost] using upper_trace popped
    · change p.upper.popCost + 4 + (p.lower.potential + rest.potential) ≤
        24 + (p.lower.potential + p.upper.potential)
      omega
    · change p.lower.decode.mass + p.upper.decode.mass =
        p.lower.decode.mass + rest.decode.mass + (weight x + HeavyPath.mass weight r)
      linarith

/-- Equal represented fringes determine subtree sizes, even if the Chocolate
repair histories produced different shapes. -/
theorem represents_sizes {α : Type} {weight : α → ℝ} {payload : LabelledTree α → Tree}
    {cs : List (Frame α)} {p q : Stacks}
    (first : p.Represents weight payload cs) (second : q.Represents weight payload cs) :
    p.lower.decode.tree.size = q.lower.decode.tree.size ∧
    p.upper.decode.tree.size = q.upper.decode.tree.size ∧ p.tree.size = q.tree.size := by
  have lower := congrArg WeightedTree.fringeSpan (first.2.1.trans second.2.1.symm)
  have upper := congrArg WeightedTree.fringeSpan (first.2.2.trans second.2.2.symm)
  rw [WeightedTree.fringeSpan_fringe, WeightedTree.fringeSpan_fringe] at lower upper
  have l : p.lower.decode.tree.size = q.lower.decode.tree.size := by omega
  have r : p.upper.decode.tree.size = q.upper.decode.tree.size := by omega
  exact ⟨l, r, by simp only [Stacks.tree, Tree.size, Tree.mirror_size, l, r]⟩

end RotationBST.HeavyPath.Paired.Exposure
