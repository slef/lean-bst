module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Paired.Interruption.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Paired.Interruption.Results
open PopTart PopTart.Chocolate StaticTree
open _root_.RotationBST.Tree (depth)

theorem lower_pop {p : Stacks} {crumb : WeightedTree} {rest : Layer}
    (popped : p.lower.pop = some (crumb, rest)) :
    Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, depth t x ≤ 4 * depth p.tree x + 10) ⟨p.tree, []⟩
      ⟨.node crumb.tree (Stacks.tree ⟨rest, p.upper⟩), []⟩ (p.lower.popCost + 4) :=
  RotationBST.HeavyPath.Paired.Interruption.lower_pop popped

theorem upper_pop {p : Stacks} {crumb : WeightedTree} {rest : Layer}
    (popped : p.upper.pop = some (crumb, rest)) :
    Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, depth t x ≤ 4 * depth p.tree x + 10) ⟨p.tree, []⟩
      ⟨.node (Stacks.tree ⟨p.lower, rest⟩) crumb.tree.mirror, []⟩ (p.upper.popCost + 4) :=
  RotationBST.HeavyPath.Paired.Interruption.upper_pop popped

theorem lower_push (p : Stacks) (payload : Tree) (weight : ℝ) :
    Pointer.TraceWithin (fun t => t.size = (Tree.node payload p.tree).size ∧
      ∀ x, depth t x ≤ 4 * depth (.node payload p.tree) x + 16)
      ⟨.node payload p.tree, []⟩
      ⟨Stacks.tree ⟨p.lower.push (.leaf payload weight), p.upper⟩, []⟩ (p.lower.pushCost + 4) :=
  RotationBST.HeavyPath.Paired.Interruption.lower_push p payload weight

theorem upper_push (p : Stacks) (payload : Tree) (weight : ℝ) :
    Pointer.TraceWithin (fun t => t.size = (Tree.node p.tree payload).size ∧
      ∀ x, depth t x ≤ 4 * depth (.node p.tree payload) x + 16)
      ⟨.node p.tree payload, []⟩
      ⟨Stacks.tree ⟨p.lower, p.upper.push (.leaf payload.mirror weight)⟩, []⟩ (p.upper.pushCost + 4) :=
  RotationBST.HeavyPath.Paired.Interruption.upper_push p payload weight

theorem push_frame {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (frame : LabelledCursor.Frame α) (p : Stacks) :
    Pointer.TraceWithin (fun t => t.size = (Pointer.plug [replaceFrame payload frame] p.tree).size ∧
      ∀ x, depth t x ≤ 4 * depth (Pointer.plug [replaceFrame payload frame] p.tree) x + 16)
      ⟨Pointer.plug [replaceFrame payload frame] p.tree, []⟩
      ⟨(p.pushWith weight payload frame).tree, []⟩ (p.pushCost frame + 1) :=
  RotationBST.HeavyPath.Paired.Interruption.push_frame weight payload frame p

end RotationBST.HeavyPath.Paired.Interruption.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Paired.Interruption.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Paired.Interruption.Results allowing [
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
  RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Models.Pointer.Invariant.Definitions.Abstract]
