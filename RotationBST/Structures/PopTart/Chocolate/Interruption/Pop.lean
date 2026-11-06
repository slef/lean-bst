module

public import RotationBST.Structures.PopTart.Chocolate.Interruption.Shape
public import RotationBST.Structures.PopTart.Chocolate.Pop.Traces
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate.Interruption
open StaticTree WeightedTree
open _root_.RotationBST.Tree (depth)

private theorem short_pop {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) (short : stack.popCost ≤ 8) :
    Pointer.TraceWithin (fun t => t.size = stack.decode.tree.size ∧
      ∀ x, depth t x ≤ 4 * depth stack.decode.tree x + 8)
      ⟨stack.decode.tree, []⟩ ⟨.node crumb.tree rest.decode.tree, []⟩ stack.popCost := by
  apply (StaticTree.Trace.within_size_depth (pop_trace popped)).weaken
  intro t bound
  refine ⟨bound.1, ?_⟩
  intro x
  have localBound := bound.2 x
  change depth t x ≤ depth stack.decode.tree x + stack.popCost at localBound
  omega

/-- Recursive borrowing and local thawing preserve a population-independent
pointwise depth bound through the exact original physical pop execution. -/
theorem pop_within {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) :
    Pointer.TraceWithin (fun t => t.size = stack.decode.tree.size ∧
      ∀ x, depth t x ≤ 4 * depth stack.decode.tree x + 8)
      ⟨stack.decode.tree, []⟩ ⟨.node crumb.tree rest.decode.tree, []⟩ stack.popCost := by
  cases stack with
  | last rs icing =>
    apply short_pop popped
    cases rs <;> cases icing <;> simp [Layer.popCost, Icing.popCost]
  | next rs child icing =>
    cases rs with
    | zero => cases popped
    | two a b => exact short_pop popped (by simp [Layer.popCost])
    | three a b c => exact short_pop popped (by simp [Layer.popCost])
    | one a =>
      cases base : child.baseCrumb with
      | some block => exact short_pop popped (by simp [popCost_next, base])
      | none =>
        have result := popped
        rw [pop_next, base] at result
        cases childPop : child.pop with
        | none => simp only [childPop] at result; cases result
        | some pair =>
          rcases pair with ⟨block, suffix⟩
          cases block with
          | leaf => simp only [childPop] at result; cases result
          | node b c =>
            simp only [childPop, Option.some.injEq, Prod.mk.injEq] at result
            rcases result with ⟨rfl, rfl⟩
            have ih := pop_within childPop
            let cs : List Pointer.Frame := [.left icing.decode.tree, .right a.tree]
            let P := fun t : Tree => t.size = (Tree.node a.tree (.node child.decode.tree icing.decode.tree)).size ∧
              ∀ x, depth t x ≤ 4 * depth (.node a.tree (.node child.decode.tree icing.decode.tree)) x + 2
            have lifted : Pointer.TraceWithin (fun t => P (Pointer.plug cs t))
                ⟨child.decode.tree, []⟩ ⟨.node (.node b c : WeightedTree).tree suffix.decode.tree, []⟩ child.popCost :=
              ih.weaken (by
                intro t bound
                refine ⟨?_, borrow_depth a.tree child.decode.tree icing.decode.tree t bound.1 bound.2⟩
                change (Tree.node a.tree (.node t icing.decode.tree)).size = _
                simp only [Tree.size, bound.1])
            have first := Pointer.TraceWithin.inContext (P := P) cs lifted
              (hasTop_ne_nil (pop_hasTop childPop)) (by intro h; cases h)
            have thaw := StaticTree.Trace.within_size_depth
              (thaw_under (icing := .frozen (.node b c) suffix icing) rfl a)
            have firstEnd := first.finish
            have second : Pointer.TraceWithin (fun t => t.size =
                  (Tree.node a.tree (.node child.decode.tree icing.decode.tree)).size ∧
                ∀ x, depth t x ≤ 4 * depth (.node a.tree (.node child.decode.tree icing.decode.tree)) x + 8)
                _ _ 6 := thaw.weaken (by
              intro t bound
              refine ⟨bound.1.trans firstEnd.1, ?_⟩
              intro x
              have localBound := bound.2 x
              have earlier := firstEnd.2 x
              change depth t x ≤ depth (Tree.node a.tree (.node (.node (.node b.tree c.tree) suffix.decode.tree) icing.decode.tree)) x + 6 at localBound
              change depth (Tree.node a.tree (.node (.node (.node b.tree c.tree) suffix.decode.tree) icing.decode.tree)) x ≤ _ at earlier
              omega)
            have firstLoose := first.weaken (Q := fun t => t.size =
                (Tree.node a.tree (.node child.decode.tree icing.decode.tree)).size ∧
              ∀ x, depth t x ≤ 4 * depth (.node a.tree (.node child.decode.tree icing.decode.tree)) x + 8)
              (by intro t bound; exact ⟨bound.1, fun x => (bound.2 x).trans (by omega)⟩)
            have linked := firstLoose.append second
            rw [popCost_next, base]
            convert linked using 1 <;> (try rfl)
            simp only [cs, List.length_cons, List.length_nil]
            omega
termination_by stack

end RotationBST.PopTart.Chocolate.Interruption
