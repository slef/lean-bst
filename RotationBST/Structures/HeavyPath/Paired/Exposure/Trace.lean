module

public import RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Top.Abstract
public import RotationBST.Structures.PopTart.Mirror.Abstract
public import RotationBST.Models.Pointer.Mirror.Abstract
public import RotationBST.Models.Pointer.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired.Exposure
open PopTart PopTart.Chocolate

private theorem popped_nonempty {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) : stack.decode.tree ≠ .nil := by
  obtain ⟨_, _, rotations⟩ := (Chocolate.Results.pop_trace popped).rotations
  have sizes := rotations.size_eq
  simp only [Pointer.Config.tree, Pointer.plug, Tree.size] at sizes
  intro empty
  rw [empty, Tree.size] at sizes
  omega

/-- The popped separator becomes the new root; its right child retains the
endpoint and both residual path stacks. -/
theorem lower_trace {p : Stacks} {crumb : WeightedTree} {rest : Layer}
    (popped : p.lower.pop = some (crumb, rest)) :
    Pointer.Trace ⟨p.tree, []⟩
      ⟨.node crumb.tree (Stacks.tree ⟨rest, p.upper⟩), []⟩ (p.lower.popCost + 4) := by
  have pop := (Chocolate.Results.pop_trace popped).inContext
    (popped_nonempty popped) (by intro h; cases h) [.left p.upper.decode.tree.mirror]
  have rotate : Pointer.Trace
      ⟨.node (.node crumb.tree rest.decode.tree) p.upper.decode.tree.mirror, []⟩
      ⟨.node crumb.tree (.node rest.decode.tree p.upper.decode.tree.mirror), []⟩ 2 :=
    .step .downLeft (.step .rotateLeftChild .refl)
  have result := pop.append rotate
  convert result using 1 <;> simp only [Stacks.tree, Pointer.plug, List.length_cons, List.length_nil]
  omega

/-- The mirrored pop exposes the upper ancestor as the new root. -/
theorem upper_trace {p : Stacks} {crumb : WeightedTree} {rest : Layer}
    (popped : p.upper.pop = some (crumb, rest)) :
    Pointer.Trace ⟨p.tree, []⟩
      ⟨.node (Stacks.tree ⟨p.lower, rest⟩) crumb.tree.mirror, []⟩ (p.upper.popCost + 4) := by
  have trace := (lower_trace (p := ⟨p.upper, p.lower⟩) popped).mirror
  simpa only [Pointer.Config.mirror, Stacks.tree, Tree.mirror, Tree.mirror_mirror,
    List.map_nil] using trace

end RotationBST.HeavyPath.Paired.Exposure
