module

public import RotationBST.Bounds.StaticTree.Trace.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Abstract
public import RotationBST.Structures.PopTart.Located.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate.Interruption
open WeightedTree

/-- Every physical prefix of push has bounded depth drift, even inside an
arbitrary surrounding context and with nonempty opaque fringe payloads. -/
theorem push_prefix {stack : Layer} (valid : stack.Valid 0) (new : WeightedTree)
    (cs : List Pointer.Frame) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.pushCost ∧
      Multifinger.replay ops ⟨.node new.tree stack.decode.tree, cs⟩ =
        some ⟨(stack.push new).decode.tree, cs⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node new.tree stack.decode.tree, cs⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨(stack.push new).decode.tree, cs⟩ ∧
        ∀ x, (Tree.depth middle.tree x : ℝ) ≤
          Tree.depth (Pointer.plug cs (.node new.tree stack.decode.tree)) x +
            6 + 14 * Real.logb 2 (stack.decode.leafCount) := by
  have trace := (Chocolate.Results.push_trace stack new).under cs
  obtain ⟨ops, length, replay⟩ := Multifinger.Replay.Results.record trace
  have budget : (ops.length : ℝ) ≤ 6 + 14 * Real.logb 2 (stack.decode.leafCount) := by
    rw [length]
    have worst := Chocolate.Results.push_worst_case valid
    linarith
  refine ⟨ops, length, replay, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bound⟩ := StaticTree.Trace.Results.replay_prefix_bound replay budget cut
  refine ⟨middle, first, last, ?_⟩
  intro x
  simpa only [Pointer.Config.under, Pointer.Config.tree, List.nil_append, add_assoc] using bound x

/-- Every prefix of pop, including recursive borrowing and thawing, has the
same physical suffix and logarithmic drift from its starting tree. -/
theorem pop_prefix {stack rest : Layer} {crumb : WeightedTree} (valid : stack.Valid 0)
    (popped : stack.pop = some (crumb, rest)) (cs : List Pointer.Frame) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.popCost ∧
      Multifinger.replay ops ⟨stack.decode.tree, cs⟩ = some ⟨.node crumb.tree rest.decode.tree, cs⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨stack.decode.tree, cs⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node crumb.tree rest.decode.tree, cs⟩ ∧
        ∀ x, (Tree.depth middle.tree x : ℝ) ≤
          Tree.depth (Pointer.plug cs stack.decode.tree) x +
            6 + 10 * Real.logb 2 (stack.decode.leafCount) := by
  have trace := (Chocolate.Results.pop_trace popped).under cs
  obtain ⟨ops, length, replay⟩ := Multifinger.Replay.Results.record trace
  have budget : (ops.length : ℝ) ≤ 6 + 10 * Real.logb 2 (stack.decode.leafCount) := by
    rw [length]
    have worst := Chocolate.Results.pop_worst_case valid
    linarith
  refine ⟨ops, length, replay, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bound⟩ := StaticTree.Trace.Results.replay_prefix_bound replay budget cut
  refine ⟨middle, first, last, ?_⟩
  intro x
  simpa only [Pointer.Config.under, Pointer.Config.tree, List.nil_append, add_assoc] using bound x

/-- In the unit-weight empty-fringe case, the entire pop implementation has
logarithmic key depth, not just its completed endpoints. -/
theorem uniform_pop_prefix {stack rest : Layer} {crumb : WeightedTree} (valid : stack.Valid 0)
    (popped : stack.pop = some (crumb, rest))
    (unitWeights : ∀ subtree weight depth, SlotAt stack.decode subtree weight depth → weight = 1)
    (empty : stack.decode.EmptyFringe) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.popCost ∧
      Multifinger.replay ops ⟨stack.decode.tree, []⟩ = some ⟨.node crumb.tree rest.decode.tree, []⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨stack.decode.tree, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node crumb.tree rest.decode.tree, []⟩ ∧
        ∀ x, x < stack.decode.tree.size → (Tree.depth middle.tree x : ℝ) <
          13 + 17 * Real.logb 2 (stack.decode.leafCount) := by
  obtain ⟨ops, length, replay, prefixes⟩ := pop_prefix valid popped []
  refine ⟨ops, length, replay, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bound⟩ := prefixes cut
  refine ⟨middle, first, last, ?_⟩
  intro x inside
  have initial := Chocolate.Results.uniform_key_depth valid unitWeights empty x inside
  rw [← WeightedTree.Results.empty_count empty] at initial
  have drift := bound x
  simp only [Pointer.plug] at drift
  linarith

/-- Uniform empty-fringe push remains logarithmic throughout rebalancing. -/
theorem uniform_push_prefix {stack : Layer} (valid : stack.Valid 0)
    (unitWeights : ∀ subtree weight depth, SlotAt stack.decode subtree weight depth → weight = 1)
    (empty : stack.decode.EmptyFringe) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.pushCost ∧
      Multifinger.replay ops ⟨.node .nil stack.decode.tree, []⟩ =
        some ⟨(stack.push (.leaf .nil 1)).decode.tree, []⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node .nil stack.decode.tree, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨(stack.push (.leaf .nil 1)).decode.tree, []⟩ ∧
        ∀ x, x < stack.decode.tree.size + 1 → (Tree.depth middle.tree x : ℝ) <
          14 + 21 * Real.logb 2 (stack.decode.leafCount) := by
  obtain ⟨ops, length, replay, prefixes⟩ := push_prefix valid (.leaf .nil 1) []
  refine ⟨ops, length, replay, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bound⟩ := prefixes cut
  refine ⟨middle, first, last, ?_⟩
  intro x inside
  have drift := bound x
  change (Tree.depth middle.tree x : ℝ) ≤
    Tree.depth (.node .nil stack.decode.tree) x + 6 +
      14 * Real.logb 2 (stack.decode.leafCount) at drift
  cases x with
  | zero =>
    have height := Chocolate.Results.uniform_height valid unitWeights
    have nonnegative : (0 : ℝ) ≤ stack.decode.height := by positivity
    simp only [Tree.depth, Tree.size, Nat.lt_irrefl, ite_false, ite_true, Nat.cast_zero] at drift
    linarith
  | succ x =>
    have initial := Chocolate.Results.uniform_key_depth valid unitWeights empty x (by omega)
    rw [← WeightedTree.Results.empty_count empty] at initial
    simp only [Tree.depth, Tree.size, Nat.not_lt_zero, ite_false, Nat.succ_ne_zero,
      Nat.sub_zero, Nat.add_one_sub_one, Nat.cast_add, Nat.cast_one] at drift
    linarith

/-- For an arbitrary nonempty payload occurrence, pop preserves a weighted
interruption bound at its original rank. The extra population term accounts
for all rebalancing instructions; payload-internal depth is retained exactly. -/
theorem pop_payload_prefix {stack rest : Layer} {crumb : WeightedTree} (valid : stack.Valid 0)
    (popped : stack.pop = some (crumb, rest)) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.popCost ∧
      Multifinger.replay ops ⟨stack.decode.tree, []⟩ = some ⟨.node crumb.tree rest.decode.tree, []⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨stack.decode.tree, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node crumb.tree rest.decode.tree, []⟩ ∧
        ∀ subtree weight offset slotDepth,
          LocatedSlot stack.decode subtree weight offset slotDepth → 0 < weight →
          ∀ x, x < subtree.size → (Tree.depth middle.tree (offset + x) : ℝ) ≤
            Tree.depth subtree x + 13 + 7 * Real.logb 2 (stack.decode.mass / weight) +
              10 * Real.logb 2 (stack.decode.leafCount) := by
  obtain ⟨ops, length, replay, prefixes⟩ := pop_prefix valid popped []
  refine ⟨ops, length, replay, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bound⟩ := prefixes cut
  refine ⟨middle, first, last, ?_⟩
  intro subtree weight offset slotDepth slot positive x inside
  have drift := bound (offset + x)
  have initial := Chocolate.Results.weighted_depth valid (Located.Results.forget slot) positive
  rw [Pointer.plug, Located.Results.key_depth slot x inside] at drift
  push_cast at drift
  linarith

/-- Push has the same payload guarantee after shifting each old occurrence
past the caller-supplied new payload and separator. -/
theorem push_payload_prefix {stack : Layer} (valid : stack.Valid 0) (new : WeightedTree) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.pushCost ∧
      Multifinger.replay ops ⟨.node new.tree stack.decode.tree, []⟩ =
        some ⟨(stack.push new).decode.tree, []⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node new.tree stack.decode.tree, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨(stack.push new).decode.tree, []⟩ ∧
        ∀ subtree weight offset slotDepth,
          LocatedSlot stack.decode subtree weight offset slotDepth → 0 < weight →
          ∀ x, x < subtree.size →
            (Tree.depth middle.tree (offset + new.tree.size + 1 + x) : ℝ) ≤
              Tree.depth subtree x + 14 + 7 * Real.logb 2 (stack.decode.mass / weight) +
                14 * Real.logb 2 (stack.decode.leafCount) := by
  obtain ⟨ops, length, replay, prefixes⟩ := push_prefix valid new []
  refine ⟨ops, length, replay, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bound⟩ := prefixes cut
  refine ⟨middle, first, last, ?_⟩
  intro subtree weight offset slotDepth slot positive x inside
  have drift := bound (offset + new.tree.size + 1 + x)
  have initial := Chocolate.Results.weighted_depth valid (Located.Results.forget slot) positive
  have keyDepth := Located.Results.key_depth (LocatedSlot.right (l := new) slot) x inside
  change Tree.depth (.node new.tree stack.decode.tree) (offset + new.tree.size + 1 + x) =
    slotDepth + 1 + Tree.depth subtree x at keyDepth
  rw [Pointer.plug, keyDepth] at drift
  push_cast at drift
  linarith

end RotationBST.PopTart.Chocolate.Interruption
