module

public import RotationBST.Structures.PopTart.Chocolate.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Interruption.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.ChocolatePop
open RotationBST.PopTart
open Chocolate WeightedTree

private def leaf (w : ℝ) : WeightedTree := .leaf .nil w
private def pair (a b : ℝ) : WeightedTree := .node (leaf a) (leaf b)
private theorem leafPerfect (w : ℝ) : Perfect 0 (leaf w) := .leaf _ _
private theorem pairPerfect (a b : ℝ) : Perfect 1 (pair a b) := .node (leafPerfect a) (leafPerfect b)
private theorem leafGood (w : ℝ) (nonnegative : 0 ≤ w) : Perfect 0 (leaf w) ∧ (leaf w).Nonnegative :=
  ⟨leafPerfect w, nonnegative⟩

-- Thaw a frozen pending carry and restore its saved strict mass inequality.
private def old : Layer := .last .zero (.base (pair 1 1))
private theorem oldValid : old.Valid 1 :=
  ⟨trivial, ⟨pairPerfect 1 1, by norm_num [pair, leaf, Nonnegative]⟩, fun _ => ⟨_, rfl⟩⟩
private def ice : Icing := .frozen (pair 2 3) old (.base (leaf 3))
private theorem iceValid : ice.Valid 0 := by
  refine ⟨pairPerfect 2 3, ?_, oldValid, leafGood 3 (by norm_num), ?_, ?_⟩
  all_goals norm_num [old, pair, leaf, Nonnegative, Layer.decode, Icing.decode, Regulars.attach, mass]
private def thawState : Layer := .last (.one (leaf 7)) ice
private def thawed : Layer := .next (.two (leaf 2) (leaf 3)) old (.base (leaf 3))
private theorem thawStateValid : thawState.Valid 0 :=
  ⟨leafGood 7 (by norm_num), iceValid, by intro h; cases h⟩

example : thawState.pop = some (leaf 7, thawed) := rfl
example : thawState.popCost = 6 := rfl
example : thawed.Valid 0 :=
  Chocolate.Results.operation_valid thawStateValid (.pop thawState thawed (leaf 7) rfl)
example (cs : List Pointer.Frame) :
    Pointer.Trace ⟨thawState.decode.tree, cs⟩ ⟨.node (leaf 7).tree thawed.decode.tree, cs⟩ 6 :=
  Chocolate.Results.operation_trace (.pop thawState thawed (leaf 7) rfl : Operation 0 thawState thawed) cs

-- Borrow a single next-level base crumb without popping a nonexistent node.
private def baseBorrow : Layer := .next (.one (leaf 7)) old (.base (leaf 3))
private def baseRest : Layer := .last (.two (leaf 1) (leaf 1)) (.base (leaf 3))
example : baseBorrow.pop = some (leaf 7, baseRest) := rfl
example : baseBorrow.popCost = 4 := rfl
example : Pointer.Trace ⟨baseBorrow.decode.tree, []⟩ ⟨.node (leaf 7).tree baseRest.decode.tree, []⟩ 4 :=
  Chocolate.Results.pop_trace (stack := baseBorrow) rfl

-- Borrow recursively through two layers; the inner borrow splits a 2-crumb.
private def quad : WeightedTree := .node (pair 1 1) (pair 1 1)
private def grand : Layer := .last .zero (.base quad)
private def middle : Layer := .next (.one (pair 1 1)) grand (.base (pair 3 3))
private theorem grandValid : grand.Valid 2 :=
  ⟨trivial, ⟨.node (pairPerfect 1 1) (pairPerfect 1 1), by norm_num [quad, pair, leaf, Nonnegative]⟩,
    fun _ => ⟨_, rfl⟩⟩
private theorem middleValid : middle.Valid 1 := by
  refine ⟨⟨pairPerfect 1 1, ?_⟩, grandValid, ⟨pairPerfect 3 3, ?_⟩, (by intro h; cases h), ?_⟩
  all_goals norm_num [grand, quad, pair, leaf, Nonnegative, Layer.decode, Icing.decode, Regulars.attach, mass]
private def deep : Layer := .next (.one (leaf 7)) middle (.base (leaf 20))
private def deepRest : Layer := .next (.two (leaf 1) (leaf 1))
  (.last (.two (pair 1 1) (pair 1 1)) (.base (pair 3 3))) (.base (leaf 20))
private theorem deepValid : deep.Valid 0 := by
  refine ⟨leafGood 7 (by norm_num), middleValid, leafGood 20 (by norm_num), (by intro h; cases h), ?_⟩
  norm_num [middle, grand, quad, pair, leaf, Layer.decode, Icing.decode, Regulars.attach, mass]
example : deep.pop = some (leaf 7, deepRest) := rfl
example : deep.popCost = 14 := rfl
example : deepRest.Valid 0 :=
  Chocolate.Results.operation_valid deepValid (.pop deep deepRest (leaf 7) rfl)
example : Pointer.Trace ⟨deep.decode.tree, []⟩ ⟨.node (leaf 7).tree deepRest.decode.tree, []⟩ 14 :=
  Chocolate.Results.pop_trace (stack := deep) rfl
example : (1 + deep.popCost : ℝ) ≤ 7 + 10 * Real.logb 2 deep.decode.leafCount :=
  Chocolate.Results.pop_worst_case deepValid
example : (1 + (Operation.pop deep deepRest (leaf 7) rfl : Operation 0 deep deepRest).cost : ℝ) ≤
    7 + 14 * Real.logb 2 deep.decode.leafCount :=
  Chocolate.Results.operation_worst_case deepValid (.pop deep deepRest (leaf 7) rfl)

-- Nonmonotone pushes freeze a perfect crumb, two pops thaw it, and another
-- push/pop pair continues from the actual returned state.
private def start : Layer := .last .zero (.base (leaf 2))
private noncomputable def s1 := start.push (leaf 4)
private noncomputable def s2 := s1.push (leaf 1)
private noncomputable def s3 := s2.push (leaf 7)
private noncomputable def s4 := s3.push (leaf 0)
private def s5 : Layer := .last (.one (leaf 7)) (.solid (pair 1 4) (.base (leaf 2)))
private def finish : Layer := .last (.two (leaf 1) (leaf 4)) (.base (leaf 2))
private noncomputable def s7 := finish.push (leaf 3)
private theorem s4Pop : s4.pop = some (leaf 0, s5) := by
  norm_num [s4, s3, s2, s1, start, s5, Layer.push, Layer.pop, leaf, pair,
    Layer.decode, Icing.decode, Regulars.attach, mass]
private noncomputable def history : Program 0 start finish 8 :=
  .cons (.push start (leaf 4) (leafPerfect 4) (by norm_num [leaf, Nonnegative]))
    (.cons (.push s1 (leaf 1) (leafPerfect 1) (by norm_num [leaf, Nonnegative]))
      (.cons (.push s2 (leaf 7) (leafPerfect 7) (by norm_num [leaf, Nonnegative]))
        (.cons (.push s3 (leaf 0) (leafPerfect 0) (by norm_num [leaf, Nonnegative]))
          (.cons (.pop s4 s5 (leaf 0) s4Pop)
            (.cons (.pop s5 finish (leaf 7) rfl)
              (.cons (.push finish (leaf 3) (leafPerfect 3) (by norm_num [leaf, Nonnegative]))
                (.cons (.pop s7 finish (leaf 3) rfl) (.nil finish))))))))
example : history.cost = 10 := by
  norm_num [history, Program.cost, Operation.cost, s7, finish, s5, s4, s3, s2, s1, start,
    Layer.push, Layer.pushCost, Layer.popCost, Icing.popCost, leaf, pair,
    Layer.decode, Icing.decode, Regulars.attach, mass]
example : finish.Valid 0 ∧ history.Realizes ∧ 8 + history.cost ≤ 168 ∧
    ∀ subtree weight depth, SlotAt finish.decode subtree weight depth → 0 < weight →
      (depth : ℝ) ≤ 7 + 7 * Real.logb 2 (finish.decode.mass / weight) :=
  Chocolate.Results.weighted_sequence history (leafPerfect 2) (by norm_num [leaf, Nonnegative])

-- Empty stacks cannot pop. A one-element stack returns to its original base.
example : start.pop = none := rfl
example : (Layer.last (.one (leaf 1)) (.base (leaf 2))).pop = some (leaf 1, start) := rfl
example : (Layer.last (.one (leaf 1)) (.base (leaf 2))).popCost = 0 := rfl
example : (Layer.last (.one (leaf 1)) (.solid (leaf 2) (.base (leaf 3)))).pop = none := rfl
example : ¬ (Layer.last (.one (leaf 1)) (.solid (leaf 2) (.base (leaf 3)))).Valid 0 := by
  intro valid
  cases valid.2.1.1

-- Every interruption of a recursive fourteen-instruction borrow has an
-- executable suffix and a depth bound in the entire enclosing tree.
example (cs : List Pointer.Frame) : ∃ ops : List Multifinger.Opcode, ops.length = 14 ∧
    Multifinger.replay ops ⟨deep.decode.tree, cs⟩ = some ⟨.node .nil deepRest.decode.tree, cs⟩ ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (ops.take cut) ⟨deep.decode.tree, cs⟩ = some middle ∧
      Multifinger.replay (ops.drop cut) middle = some ⟨.node .nil deepRest.decode.tree, cs⟩ ∧
      ∀ x, (Tree.depth middle.tree x : ℝ) ≤
        Tree.depth (Pointer.plug cs deep.decode.tree) x + 6 + 10 * Real.logb 2 deep.decode.leafCount :=
  Chocolate.Interruption.Results.pop_prefix deepValid (crumb := leaf 7) (rest := deepRest) rfl cs

-- Frozen icing thawing is covered at every physical cut, not just its end.
example : ∃ ops : List Multifinger.Opcode, ops.length = 6 ∧
    Multifinger.replay ops ⟨thawState.decode.tree, []⟩ = some ⟨.node .nil thawed.decode.tree, []⟩ ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (ops.take cut) ⟨thawState.decode.tree, []⟩ = some middle ∧
      Multifinger.replay (ops.drop cut) middle = some ⟨.node .nil thawed.decode.tree, []⟩ ∧
      ∀ x, (Tree.depth middle.tree x : ℝ) ≤
        Tree.depth thawState.decode.tree x + 6 + 10 * Real.logb 2 thawState.decode.leafCount :=
  Chocolate.Interruption.Results.pop_prefix thawStateValid (crumb := leaf 7) (rest := thawed) rfl []

-- The sharper bound covers the same fourteen-instruction recursive borrow
-- in any enclosing context, without an operation-count or population term.
example (cs : List Pointer.Frame) : ∃ ops : List Multifinger.Opcode, ops.length = 14 ∧
    Multifinger.replay ops ⟨deep.decode.tree, cs⟩ = some ⟨.node .nil deepRest.decode.tree, cs⟩ ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (ops.take cut) ⟨deep.decode.tree, cs⟩ = some middle ∧
      Multifinger.replay (ops.drop cut) middle = some ⟨.node .nil deepRest.decode.tree, cs⟩ ∧
      ∀ x, Tree.depth middle.tree x ≤
        4 * Tree.depth (Pointer.plug cs deep.decode.tree) x + 8 :=
  Chocolate.Interruption.Results.pop_depth_prefix (stack := deep) (crumb := leaf 7) (rest := deepRest) rfl cs

end RotationBST.Tests.ChocolatePop
