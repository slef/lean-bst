module

public import RotationBST.Bounds.StaticTree.Trace.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.TraceDepth

private def leaf : Tree := .node .nil .nil
private def balanced : Tree := .node leaf leaf
private def initial : Pointer.Config := ⟨balanced, []⟩
private def leaning : Pointer.Config := ⟨.node .nil (.node .nil leaf), []⟩
private def ops : List Multifinger.Opcode :=
  [.downLeft, .rotateLeftChild, .downRight, .rotateRightChild]

-- Matching balanced endpoints do not imply matching depths in between.
-- The rightmost key becomes deeper after the first rotation and returns.
example : Multifinger.replay ops initial = some initial ∧
    Multifinger.replay (ops.take 2) initial = some leaning ∧
    Tree.depth initial.tree 2 = 1 ∧ Tree.depth leaning.tree 2 = 2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- The same exact code has a certified physical suffix at every cut.
example (cut : Nat) : ∃ middle,
    Multifinger.replay (ops.take cut) initial = some middle ∧
    Multifinger.replay (ops.drop cut) middle = some initial ∧
    ∀ x, Tree.depth middle.tree x ≤
      min (Tree.depth initial.tree x + (ops.take cut).length)
        (Tree.depth initial.tree x + (ops.drop cut).length) :=
  StaticTree.Trace.Results.replay_prefix_depth (ops := ops) (s := initial) (t := initial) rfl cut

-- A cut after the program terminates is the final state with an empty suffix.
example : Multifinger.replay (ops.take 99) initial = some initial ∧
    Multifinger.replay (ops.drop 99) initial = some initial := ⟨rfl, rfl⟩

-- Rotation at depth one, inside an opaque parent context, has the same
-- pointwise one-level depth bound for every original inorder rank.
example (x : Nat) :
    Tree.depth (.node (.node .nil (.node .nil .nil)) leaf) x ≤
      Tree.depth (.node (.node leaf .nil) leaf) x + 1 :=
  StaticTree.Trace.Results.rotate_depth (.inLeft .right) x

-- Reflection preserves the bound for all totalized ranks, including values
-- beyond the end of the tree. Existing ranks reverse their identities.
example (x : Nat) : Tree.depth leaning.tree.mirror x ≤ Tree.depth balanced.mirror x + 1 := by
  have bound : ∀ y, Tree.depth leaning.tree y ≤ 1 * Tree.depth balanced y + 1 := by
    intro y
    simpa only [Nat.one_mul] using StaticTree.Trace.Results.rotate_depth (s := balanced) (t := leaning.tree) .right y
  simpa only [Nat.one_mul] using StaticTree.Trace.Results.mirror_bound (s := balanced) (t := leaning.tree) (by decide : 1 ≤ 1) rfl bound x

end RotationBST.Tests.TraceDepth
