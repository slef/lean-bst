module
public import RotationBST.Structures.PopTart.Chocolate.Interruption.Shape
public import RotationBST.Structures.PopTart.Chocolate.Traces
import Mathlib.Tactic
@[expose] public section
namespace RotationBST.PopTart.Chocolate.Interruption
open StaticTree WeightedTree
open _root_.RotationBST.Tree (depth)
private theorem carry_depth (new a b c child icing t : Tree)
    (size : t.size = (Tree.node (.node b c) child).size)
    (bound : ∀ x, depth t x ≤ 4 * depth (.node (.node b c) child) x + 8) :
    ∀ x, depth (.node new (.node a (.node t icing))) x ≤
      4 * depth (.node new (.node a (.node b (.node c (.node child icing))))) x + 8 := by
  apply right_bound
  apply right_bound
  intro x
  have rotations : Rotations (.node b (.node c (.node child icing)))
      (.node (.node (.node b c) child) icing) 2 := .step .left (.step .left .refl)
  have drift := StaticTree.Trace.rotations_depth rotations x
  have localBound := bound x
  by_cases inside : x < (Tree.node (.node b c) child).size
  · have inside' : x < t.size := by rw [size]; exact inside
    rw [depth, ite_eq_left inside] at drift
    rw [depth, ite_eq_left inside']
    omega
  · have inside' : ¬ x < t.size := by rw [size]; exact inside
    rw [depth, ite_eq_right inside] at drift
    rw [depth, ite_eq_right inside', size]
    omega
private theorem short_push (stack : Layer) (new : WeightedTree) (short : stack.pushCost ≤ 8) :
    Pointer.TraceWithin (fun t => t.size = (Tree.node new.tree stack.decode.tree).size ∧
      ∀ x, depth t x ≤ 4 * depth (.node new.tree stack.decode.tree) x + 8)
      ⟨.node new.tree stack.decode.tree, []⟩ ⟨(stack.push new).decode.tree, []⟩ stack.pushCost := by
  apply (StaticTree.Trace.within_size_depth (push_trace stack new)).weaken
  intro t bound
  refine ⟨bound.1, ?_⟩
  intro x
  have localBound := bound.2 x
  change depth t x ≤ depth (.node new.tree stack.decode.tree) x + stack.pushCost at localBound
  omega

/-- Every key stays within four times its starting depth plus eight throughout
push. The bound is independent of population, weights, and recursive carry
length, and the exact original physical cost is retained. -/
theorem push_within (stack : Layer) (new : WeightedTree) :
    Pointer.TraceWithin (fun t => t.size = (Tree.node new.tree stack.decode.tree).size ∧
      ∀ x, depth t x ≤ 4 * depth (.node new.tree stack.decode.tree) x + 8)
      ⟨.node new.tree stack.decode.tree, []⟩ ⟨(stack.push new).decode.tree, []⟩ stack.pushCost := by
  classical
  cases stack with
  | last rs icing =>
    apply short_push
    cases rs <;> simp [Layer.pushCost]
  | next rs child icing =>
    cases rs with
    | zero => exact short_push _ new (by simp [Layer.pushCost])
    | one a => exact short_push _ new (by simp [Layer.pushCost])
    | two a b => exact short_push _ new (by simp [Layer.pushCost])
    | three a b c =>
      by_cases thin : (.node b c : WeightedTree).mass + child.decode.mass < icing.decode.mass
      · have join : Pointer.Trace
            ⟨.node b.tree (.node c.tree (.node child.decode.tree icing.decode.tree)), []⟩
            ⟨.node (.node b.tree c.tree) (.node child.decode.tree icing.decode.tree), []⟩ 2 :=
          .step .downRight (.step .rotateRightChild .refl)
        have move : Pointer.Trace
            ⟨.node (.node b.tree c.tree) (.node child.decode.tree icing.decode.tree), []⟩
            ⟨.node (.node (.node b.tree c.tree) child.decode.tree) icing.decode.tree, []⟩ 2 :=
          .step .downRight (.step .rotateRightChild .refl)
        have first := (join.append move).inContext (by intro h; cases h) (by intro h; cases h)
          [.right a.tree, .right new.tree]
        have firstWithin := StaticTree.Trace.within_size_depth first
        have ih := push_within child (.node b c)
        have live : (child.push (.node b c)).decode.tree ≠ .nil := by
          intro empty
          have size := ih.finish.1
          change (child.push (.node b c)).decode.tree.size = _ at size
          rw [empty] at size
          simp only [Tree.size, WeightedTree.tree] at size
          omega
        let cs : List Pointer.Frame := [.left icing.decode.tree, .right a.tree, .right new.tree]
        have lifted := ih.weaken (Q := fun t =>
          (Pointer.plug cs t).size = (Tree.node new.tree (Layer.next (.three a b c) child icing).decode.tree).size ∧
          ∀ x, depth (Pointer.plug cs t) x ≤
            4 * depth (.node new.tree (Layer.next (.three a b c) child icing).decode.tree) x + 8) (by
          intro t bound
          have size := bound.1
          change t.size = (Tree.node (.node b.tree c.tree) child.decode.tree).size at size
          refine ⟨?_, ?_⟩
          · change (Tree.node new.tree (.node a.tree (.node t icing.decode.tree))).size =
              (Tree.node new.tree (.node a.tree (.node b.tree (.node c.tree (.node child.decode.tree icing.decode.tree))))).size
            simp only [Tree.size] at size ⊢
            omega
          · exact carry_depth new.tree a.tree b.tree c.tree child.decode.tree icing.decode.tree t size bound.2)
        have second := Pointer.TraceWithin.inContext
          (P := fun t => t.size = (Tree.node new.tree (Layer.next (.three a b c) child icing).decode.tree).size ∧
            ∀ x, depth t x ≤ 4 * depth (.node new.tree (Layer.next (.three a b c) child icing).decode.tree) x + 8)
          (s := .node (.node b.tree c.tree) child.decode.tree) cs lifted (by intro h; cases h) live
        have firstBound : Pointer.TraceWithin (fun t =>
            t.size = (Tree.node new.tree (Layer.next (.three a b c) child icing).decode.tree).size ∧
            ∀ x, depth t x ≤ 4 * depth (.node new.tree (Layer.next (.three a b c) child icing).decode.tree) x + 8)
            _ _ 8 := firstWithin.weaken (by
          intro t bound
          refine ⟨bound.1, ?_⟩
          intro x
          have localBound := bound.2 x
          change depth t x ≤ depth (.node new.tree (Layer.next (.three a b c) child icing).decode.tree) x + 8 at localBound
          omega)
        have linked := firstBound.append second
        simp only [Layer.push, Layer.pushCost, thin, ite_true]
        convert linked using 1 <;> (try rfl)
        simp only [cs, List.length_cons, List.length_nil]
        omega
      · exact short_push _ new (by simp only [Layer.pushCost, thin, ite_false]; omega)
termination_by stack

end RotationBST.PopTart.Chocolate.Interruption
