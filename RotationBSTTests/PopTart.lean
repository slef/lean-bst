module

public import RotationBST.Structures.PopTart.Vanilla.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.PopTart
open RotationBST.PopTart

private def bottom : WeightedTree := .leaf .nil 1
private def older : WeightedTree := Vanilla.push .nil 1 bottom
private def middle : WeightedTree := Vanilla.push .nil 2 older
private def stack : WeightedTree := Vanilla.push .nil 4 middle

private theorem bottomValid : Vanilla.Valid bottom := .leaf .nil 1 (by norm_num)
private theorem olderValid : Vanilla.Valid older :=
  Vanilla.Results.push_valid bottomValid .nil 1 (by norm_num [bottom, WeightedTree.mass])
private theorem middleValid : Vanilla.Valid middle :=
  Vanilla.Results.push_valid olderValid .nil 2 (by norm_num [older, bottom, Vanilla.push, WeightedTree.mass])
private theorem stackValid : Vanilla.Valid stack :=
  Vanilla.Results.push_valid middleValid .nil 4 (by norm_num [middle, older, bottom, Vanilla.push, WeightedTree.mass])

-- Identical empty subtree shapes occupy different slots with different weights.
example : WeightedTree.SlotAt stack .nil 4 1 := .left (.leaf .nil 4)
example : WeightedTree.SlotAt stack .nil 2 2 := .right (.left (.leaf .nil 2))
example : stack.mass = 8 := by norm_num [stack, middle, older, bottom, Vanilla.push, WeightedTree.mass]

private theorem bottomSlot : WeightedTree.SlotAt stack .nil 1 3 :=
  .right (.right (.right (.leaf .nil 1)))

example : (2 : ℝ) ^ 3 ≤ 2 * stack.mass := by
  simpa only [mul_one] using Vanilla.Results.depth_mass stackValid bottomSlot

example : (3 : ℝ) ≤ 1 + Real.logb 2 stack.mass := by
  simpa only [div_one, Nat.cast_ofNat] using Vanilla.Results.depth_log stackValid bottomSlot (by norm_num)

-- Popping retains the old weighted structure exactly, and preserves validity.
example : Vanilla.pop stack = some ((Tree.nil, 4), middle) := rfl
example : Vanilla.Valid middle ∧ 0 < (4 : ℝ) ∧ middle.mass ≤ 4 := by
  have restored := Vanilla.Results.pop_valid stackValid (show Vanilla.pop stack = some ((Tree.nil, 4), middle) from rfl)
  exact ⟨restored.1, by norm_num, restored.2.2⟩

-- All roots remain in the tree until the caller transfers the separator.
-- Arbitrary surrounding contexts do not add rebalancing instructions.
example (cs : List Pointer.Frame) :
    Pointer.Trace ⟨stack.tree, cs⟩ ⟨Tree.node Tree.nil middle.tree, cs⟩ 0 :=
  Vanilla.Results.operation (.pop stack middle .nil 4 rfl) cs

example (cs : List Pointer.Frame) :
    Pointer.Trace ⟨Tree.node Tree.nil middle.tree, cs⟩ ⟨stack.tree, cs⟩ 0 :=
  Vanilla.Results.operation (.push .nil 4 middle) cs

-- A frozen slot is opaque to the outer stack. Its root is physically reachable
-- in exactly one move even though it is not an empty external leaf.
private def frozen : Tree := .node (.node .nil .nil) (.node .nil .nil)
private def iced : WeightedTree := Vanilla.push frozen 7 older
private theorem icedValid : Vanilla.Valid iced :=
  Vanilla.Results.push_valid olderValid frozen 7 (by norm_num [older, bottom, Vanilla.push, WeightedTree.mass])

example : ∃ cs : List Pointer.Frame, cs.length = 1 ∧ Pointer.plug cs frozen = iced.tree ∧
    Pointer.Trace ⟨iced.tree, []⟩ ⟨frozen, cs⟩ 1 ∧
    (1 : ℝ) ≤ 1 + Real.logb 2 (iced.mass / 7) := by
  simpa only [Nat.zero_add, Nat.cast_one] using
    Vanilla.Results.access_slot icedValid (.left (.leaf frozen 7)) (by norm_num) (by decide)

-- Zero-weight empty fringes remain valid, but the logarithmic theorem requires
-- the queried weight to be positive. A positive slot above a zero fringe is tight.
private def zeroBottom : WeightedTree := .leaf .nil 0
private theorem zeroValid : Vanilla.Valid zeroBottom := .leaf .nil 0 le_rfl
private theorem oneValid : Vanilla.Valid (Vanilla.push .nil 1 zeroBottom) :=
  Vanilla.Results.push_valid zeroValid .nil 1 (by norm_num [zeroBottom, WeightedTree.mass])

example : (1 : ℝ) ≤ 1 + Real.logb 2 ((Vanilla.push .nil 1 zeroBottom).mass / 1) := by
  simpa only [Nat.zero_add, Nat.cast_one] using
    Vanilla.Results.depth_log oneValid (.left (.leaf .nil 1)) (by norm_num)

example : Vanilla.pop zeroBottom = none := rfl
example : ¬ Vanilla.Valid (.leaf .nil (-1)) := by
  intro valid
  cases valid with
  | leaf t w nonnegative => norm_num at nonnegative

-- A light new slot cannot establish the doubling invariant.
example : ¬ Vanilla.Valid (Vanilla.push .nil 1 older) := by
  intro valid
  cases valid with
  | push t w tailValid dominates => norm_num [older, bottom, Vanilla.push, WeightedTree.mass] at dominates

end RotationBST.Tests.PopTart
