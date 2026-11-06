module

public import RotationBST.Structures.PopTart.Chocolate.Interruption.Push
public import RotationBST.Structures.PopTart.Chocolate.Interruption.Pop
public import RotationBST.Structures.PopTart.Chocolate.Abstract
public import RotationBST.Structures.PopTart.Located.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate.Interruption
open WeightedTree

/-- Pointwise depth control for every physical push prefix in an arbitrary
surrounding context, without any population or operation-length term. -/
theorem push_depth_prefix (stack : Layer) (new : WeightedTree) (cs : List Pointer.Frame) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.pushCost ∧
      Multifinger.replay ops ⟨.node new.tree stack.decode.tree, cs⟩ = some ⟨(stack.push new).decode.tree, cs⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node new.tree stack.decode.tree, cs⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨(stack.push new).decode.tree, cs⟩ ∧
        ∀ x, Tree.depth middle.tree x ≤
          4 * Tree.depth (Pointer.plug cs (.node new.tree stack.decode.tree)) x + 8 := by
  have certified := push_within stack new
  have contextual := certified.weaken (Q := fun t => ∀ x,
    Tree.depth (Pointer.plug cs t) x ≤
      4 * Tree.depth (Pointer.plug cs (.node new.tree stack.decode.tree)) x + 8)
    (by intro t bounds; exact context_depth cs bounds.1 bounds.2)
  exact (Pointer.TraceWithin.under (P := fun t => ∀ x, Tree.depth t x ≤
    4 * Tree.depth (Pointer.plug cs (.node new.tree stack.decode.tree)) x + 8) cs contextual).record

/-- The same pointwise bound covers recursive pop, including borrowing and
thawing, with an unchanged cursor context and the original exact cost. -/
theorem pop_depth_prefix {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) (cs : List Pointer.Frame) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.popCost ∧
      Multifinger.replay ops ⟨stack.decode.tree, cs⟩ = some ⟨.node crumb.tree rest.decode.tree, cs⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨stack.decode.tree, cs⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node crumb.tree rest.decode.tree, cs⟩ ∧
        ∀ x, Tree.depth middle.tree x ≤
          4 * Tree.depth (Pointer.plug cs stack.decode.tree) x + 8 := by
  have certified := pop_within popped
  have contextual := certified.weaken (Q := fun t => ∀ x,
    Tree.depth (Pointer.plug cs t) x ≤
      4 * Tree.depth (Pointer.plug cs stack.decode.tree) x + 8)
    (by intro t bounds; exact context_depth cs bounds.1 bounds.2)
  exact (Pointer.TraceWithin.under (P := fun t => ∀ x, Tree.depth t x ≤
    4 * Tree.depth (Pointer.plug cs stack.decode.tree) x + 8) cs contextual).record

/-- Weighted payload access throughout pop. Unlike the earlier drift bound,
this has no logarithmic population term. Frozen occurrences remain distinct. -/
theorem pop_weighted_prefix {stack rest : Layer} {crumb : WeightedTree} (valid : stack.Valid 0)
    (popped : stack.pop = some (crumb, rest)) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.popCost ∧
      Multifinger.replay ops ⟨stack.decode.tree, []⟩ = some ⟨.node crumb.tree rest.decode.tree, []⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨stack.decode.tree, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node crumb.tree rest.decode.tree, []⟩ ∧
        ∀ subtree weight offset slotDepth,
          LocatedSlot stack.decode subtree weight offset slotDepth → 0 < weight →
          ∀ x, x < subtree.size → (Tree.depth middle.tree (offset + x) : ℝ) ≤
            4 * Tree.depth subtree x + 36 + 28 * Real.logb 2 (stack.decode.mass / weight) := by
  obtain ⟨ops, length, replay, prefixes⟩ := pop_depth_prefix popped []
  refine ⟨ops, length, replay, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bounds⟩ := prefixes cut
  refine ⟨middle, first, last, ?_⟩
  intro subtree weight offset slotDepth slot positive x inside
  have bound := bounds (offset + x)
  rw [Pointer.plug, Located.Results.key_depth slot x inside] at bound
  have castBound : (Tree.depth middle.tree (offset + x) : ℝ) ≤
      4 * ((slotDepth : ℝ) + Tree.depth subtree x) + 8 := by exact_mod_cast bound
  have initial := Chocolate.Results.weighted_depth valid (Located.Results.forget slot) positive
  linarith

/-- Old payloads retain a purely weighted bound throughout push. Their rank
shift includes the entire inserted subtree and its new separator. -/
theorem push_weighted_prefix {stack : Layer} (valid : stack.Valid 0) (new : WeightedTree) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.pushCost ∧
      Multifinger.replay ops ⟨.node new.tree stack.decode.tree, []⟩ = some ⟨(stack.push new).decode.tree, []⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node new.tree stack.decode.tree, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨(stack.push new).decode.tree, []⟩ ∧
        ∀ subtree weight offset slotDepth,
          LocatedSlot stack.decode subtree weight offset slotDepth → 0 < weight →
          ∀ x, x < subtree.size →
            (Tree.depth middle.tree (offset + new.tree.size + 1 + x) : ℝ) ≤
              4 * Tree.depth subtree x + 40 + 28 * Real.logb 2 (stack.decode.mass / weight) := by
  obtain ⟨ops, length, replay, prefixes⟩ := push_depth_prefix stack new []
  refine ⟨ops, length, replay, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bounds⟩ := prefixes cut
  refine ⟨middle, first, last, ?_⟩
  intro subtree weight offset slotDepth slot positive x inside
  have bound := bounds (offset + new.tree.size + 1 + x)
  have shift : Tree.depth (.node new.tree stack.decode.tree) (offset + new.tree.size + 1 + x) =
      Tree.depth stack.decode.tree (offset + x) + 1 := by
    rw [Tree.depth, ite_eq_right (by omega), ite_eq_right (by omega)]
    congr 1
    congr 1
    omega
  rw [Pointer.plug, shift, Located.Results.key_depth slot x inside] at bound
  have castBound : (Tree.depth middle.tree (offset + new.tree.size + 1 + x) : ℝ) ≤
      4 * ((slotDepth : ℝ) + Tree.depth subtree x + 1) + 8 := by exact_mod_cast bound
  have initial := Chocolate.Results.weighted_depth valid (Located.Results.forget slot) positive
  linarith

end RotationBST.PopTart.Chocolate.Interruption
