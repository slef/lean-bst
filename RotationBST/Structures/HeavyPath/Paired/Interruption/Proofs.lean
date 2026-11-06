module

public import RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Interruption.Abstract
public import RotationBST.Bounds.StaticTree.Trace.Mirror
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired.Interruption
open PopTart PopTart.Chocolate StaticTree
open _root_.RotationBST.Tree (depth)

/-- Expose the lower separator through the certified pop and its final
rotation. All intermediate trees retain a pointwise depth bound. -/
theorem lower_pop {p : Stacks} {crumb : WeightedTree} {rest : Layer}
    (popped : p.lower.pop = some (crumb, rest)) :
    Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, depth t x ≤ 4 * depth p.tree x + 10) ⟨p.tree, []⟩
      ⟨.node crumb.tree (Stacks.tree ⟨rest, p.upper⟩), []⟩ (p.lower.popCost + 4) := by
  have certified := Chocolate.Interruption.Results.pop_within popped
  have live : p.lower.decode.tree ≠ .nil := by
    intro empty
    have size := certified.finish.1
    change (Tree.node crumb.tree rest.decode.tree).size = p.lower.decode.tree.size at size
    rw [empty] at size
    simp only [Tree.size] at size
    omega
  have repair := StaticTree.Trace.within_embed [.left p.upper.decode.tree.mirror]
    (by decide : 1 ≤ 4) certified live (by intro h; cases h)
  have rotate : Pointer.Trace
      ⟨.node (.node crumb.tree rest.decode.tree) p.upper.decode.tree.mirror, []⟩
      ⟨.node crumb.tree (.node rest.decode.tree p.upper.decode.tree.mirror), []⟩ 2 :=
    .step .downLeft (.step .rotateLeftChild .refl)
  have final := repair.finish
  have tail : Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, depth t x ≤ 4 * depth p.tree x + 10) _ _ 2 :=
    (StaticTree.Trace.within_size_depth rotate).weaken (by
      intro t bound
      refine ⟨bound.1.trans final.1, ?_⟩
      intro x
      have first := bound.2 x
      have last := final.2 x
      change depth t x ≤ depth (Tree.node (.node crumb.tree rest.decode.tree) p.upper.decode.tree.mirror) x + 2 at first
      change depth (Tree.node (.node crumb.tree rest.decode.tree) p.upper.decode.tree.mirror) x ≤ 4 * depth p.tree x + 8 at last
      omega)
  have earlier := repair.weaken (Q := fun t => t.size = p.tree.size ∧
      ∀ x, depth t x ≤ 4 * depth p.tree x + 10)
    (by
      intro t bound
      change t.size = p.tree.size ∧ ∀ x, depth t x ≤ 4 * depth p.tree x + 8 at bound
      exact ⟨bound.1, fun x => (bound.2 x).trans (by omega)⟩)
  have result := earlier.append tail
  convert result using 1 <;> (try rfl)
  simp only [List.length_cons, List.length_nil]
  omega

/-- Reflection handles the upper separator with exactly the same constants. -/
theorem upper_pop {p : Stacks} {crumb : WeightedTree} {rest : Layer}
    (popped : p.upper.pop = some (crumb, rest)) :
    Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, depth t x ≤ 4 * depth p.tree x + 10) ⟨p.tree, []⟩
      ⟨.node (Stacks.tree ⟨p.lower, rest⟩) crumb.tree.mirror, []⟩ (p.upper.popCost + 4) := by
  have mirrored := StaticTree.Trace.within_mirror_depth
    (a := ⟨Stacks.tree ⟨p.upper, p.lower⟩, []⟩) (constant := 10) (by decide : 1 ≤ 4)
    (lower_pop (p := ⟨p.upper, p.lower⟩) popped)
  simpa only [Pointer.Config.mirror, Pointer.Config.tree, Pointer.plug, Stacks.tree,
    Tree.mirror, Tree.mirror_mirror, Tree.mirror_size, List.map_nil] using mirrored

/-- Raise the endpoint and push its new lower ancestor. The caller's separator
is already present; all navigation and rotations are counted. -/
theorem lower_push (p : Stacks) (payload : Tree) (weight : ℝ) :
    Pointer.TraceWithin (fun t => t.size = (Tree.node payload p.tree).size ∧
      ∀ x, depth t x ≤ 4 * depth (.node payload p.tree) x + 16)
      ⟨.node payload p.tree, []⟩
      ⟨Stacks.tree ⟨p.lower.push (.leaf payload weight), p.upper⟩, []⟩ (p.lower.pushCost + 4) := by
  have raised : Pointer.Trace ⟨.node payload p.tree, []⟩
      ⟨.node (.node payload p.lower.decode.tree) p.upper.decode.tree.mirror, []⟩ 2 :=
    .step .downRight (.step .rotateRightChild .refl)
  have first := StaticTree.Trace.within_size_depth raised
  have certified := Chocolate.Interruption.Results.push_within p.lower (.leaf payload weight)
  have live : (p.lower.push (.leaf payload weight)).decode.tree ≠ .nil := by
    intro empty
    have size := certified.finish.1
    change (p.lower.push (.leaf payload weight)).decode.tree.size = (Tree.node payload p.lower.decode.tree).size at size
    rw [empty] at size
    simp only [Tree.size] at size
    omega
  have repair := StaticTree.Trace.within_embed [.left p.upper.decode.tree.mirror]
    (by decide : 1 ≤ 4) certified (by intro h; cases h) live
  have boundary := first.finish
  have later := repair.weaken (Q := fun t => t.size = (Tree.node payload p.tree).size ∧
      ∀ x, depth t x ≤ 4 * depth (.node payload p.tree) x + 16) (by
    intro t bound
    refine ⟨bound.1.trans boundary.1, ?_⟩
    intro x
    have original := boundary.2 x
    have localBound := bound.2 x
    change depth (Tree.node (.node payload p.lower.decode.tree) p.upper.decode.tree.mirror) x ≤
      depth (.node payload p.tree) x + 2 at original
    change depth t x ≤ 4 * depth (Tree.node (.node payload p.lower.decode.tree) p.upper.decode.tree.mirror) x + 8 at localBound
    omega)
  have earlier := first.weaken (Q := fun t => t.size = (Tree.node payload p.tree).size ∧
      ∀ x, depth t x ≤ 4 * depth (.node payload p.tree) x + 16) (by
    intro t bound
    refine ⟨bound.1, ?_⟩
    intro x
    have localBound := bound.2 x
    change depth t x ≤ depth (.node payload p.tree) x + 2 at localBound
    omega)
  have result := earlier.append later
  convert result using 1 <;> (try rfl)
  simp only [List.length_cons, List.length_nil]
  omega

/-- The mirrored upper insertion preserves the physical payload orientation. -/
theorem upper_push (p : Stacks) (payload : Tree) (weight : ℝ) :
    Pointer.TraceWithin (fun t => t.size = (Tree.node p.tree payload).size ∧
      ∀ x, depth t x ≤ 4 * depth (.node p.tree payload) x + 16)
      ⟨.node p.tree payload, []⟩
      ⟨Stacks.tree ⟨p.lower, p.upper.push (.leaf payload.mirror weight)⟩, []⟩ (p.upper.pushCost + 4) := by
  have mirrored := StaticTree.Trace.within_mirror_depth
    (a := ⟨.node payload.mirror (Stacks.tree ⟨p.upper, p.lower⟩), []⟩)
    (constant := 16) (by decide : 1 ≤ 4)
    (lower_push ⟨p.upper, p.lower⟩ payload.mirror weight)
  simpa only [Pointer.Config.mirror, Pointer.Config.tree, Pointer.plug, Stacks.tree,
    Tree.mirror, Tree.mirror_mirror, Tree.mirror_size, List.map_nil] using mirrored

/-- Reattach an arbitrary source ancestor and its restructured light payload. -/
theorem push_frame {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (frame : LabelledCursor.Frame α) (p : Stacks) :
    Pointer.TraceWithin (fun t => t.size = (Pointer.plug [replaceFrame payload frame] p.tree).size ∧
      ∀ x, depth t x ≤ 4 * depth (Pointer.plug [replaceFrame payload frame] p.tree) x + 16)
      ⟨Pointer.plug [replaceFrame payload frame] p.tree, []⟩
      ⟨(p.pushWith weight payload frame).tree, []⟩ (p.pushCost frame + 1) := by
  cases frame with
  | left x r =>
    simpa only [replaceFrame, Pointer.plug, Stacks.pushWith, Stacks.pushCost, Nat.add_assoc] using
      (upper_push p (payload r) (weight x + mass weight r))
  | right l x =>
    simpa only [replaceFrame, Pointer.plug, Stacks.pushWith, Stacks.pushCost, Nat.add_assoc] using
      (lower_push p (payload l) (mass weight l + weight x))

end RotationBST.HeavyPath.Paired.Interruption
