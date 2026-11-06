module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Paired.Exposure.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Paired.Exposure.Results
open PopTart PopTart.Chocolate LabelledCursor

theorem lower_trace {p : Stacks} {crumb : WeightedTree} {rest : Layer}
    (popped : p.lower.pop = some (crumb, rest)) :
    Pointer.Trace ⟨p.tree, []⟩
      ⟨.node crumb.tree (Stacks.tree ⟨rest, p.upper⟩), []⟩ (p.lower.popCost + 4) :=
  RotationBST.HeavyPath.Paired.Exposure.lower_trace popped

theorem upper_trace {p : Stacks} {crumb : WeightedTree} {rest : Layer}
    (popped : p.upper.pop = some (crumb, rest)) :
    Pointer.Trace ⟨p.tree, []⟩
      ⟨.node (Stacks.tree ⟨p.lower, rest⟩) crumb.tree.mirror, []⟩ (p.upper.popCost + 4) :=
  RotationBST.HeavyPath.Paired.Exposure.upper_trace popped

theorem empty_represents {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) :
    Stacks.empty.Represents weight payload [] :=
  RotationBST.HeavyPath.Paired.Exposure.empty_represents weight payload

theorem push_represents {α : Type} {weight : α → ℝ} {payload : LabelledTree α → Tree}
    {cs : List (Frame α)} {p : Stacks} (represented : p.Represents weight payload cs)
    (frame : Frame α) (nonnegative : 0 ≤ frameMass weight frame) :
    (p.pushWith weight payload frame).Represents weight payload (cs ++ [frame]) :=
  RotationBST.HeavyPath.Paired.Exposure.push_represents represented frame nonnegative

theorem build_represents {α : Type} {weight : α → ℝ} (payload : LabelledTree α → Tree)
    (cs : List (Frame α)) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.buildWith weight payload cs Stacks.empty).Represents weight payload cs :=
  RotationBST.HeavyPath.Paired.Exposure.build_represents payload cs nonnegative

theorem expose_frame {α : Type} {weight : α → ℝ} {payload : LabelledTree α → Tree}
    {cs : List (Frame α)} {frame : Frame α} {p : Stacks}
    (represented : p.Represents weight payload (cs ++ [frame])) :
    ∃ rest : Stacks, rest.Represents weight payload cs ∧
      Pointer.Trace ⟨p.tree, []⟩ ⟨Pointer.plug [replaceFrame payload frame] rest.tree, []⟩
        (p.exposeCost frame) ∧
      p.exposeCost frame + rest.potential ≤ 24 + p.potential ∧
      p.mass = rest.mass + frameMass weight frame :=
  RotationBST.HeavyPath.Paired.Exposure.expose_frame represented

theorem represents_sizes {α : Type} {weight : α → ℝ} {payload : LabelledTree α → Tree}
    {cs : List (Frame α)} {p q : Stacks}
    (first : p.Represents weight payload cs) (second : q.Represents weight payload cs) :
    p.lower.decode.tree.size = q.lower.decode.tree.size ∧
    p.upper.decode.tree.size = q.upper.decode.tree.size ∧ p.tree.size = q.tree.size :=
  RotationBST.HeavyPath.Paired.Exposure.represents_sizes first second

end RotationBST.HeavyPath.Paired.Exposure.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Paired.Exposure.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Paired.Exposure.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract]
