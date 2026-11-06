module

public import RotationBST.Structures.HeavyPath.Finger.Transfer.Exposure.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.FingerRecursiveTransfer
open HeavyPath HeavyPath.Finger HeavyPath.Recursive
open PopTart PopTart.Chocolate

private def leaf (x : Nat) : LabelledTree Nat := .node .nil x .nil
private def child : LabelledTree Nat := .node (leaf 0) 1 (leaf 2)
private def empty : Layer := .last .zero (.base (.leaf .nil 0))
private noncomputable def leftPair : Finger.Pair :=
  ⟨.last (.one (.leaf (rebuild (fun _ => 1) child).mirror 5)) (.base (.leaf .nil 0)), empty⟩
private noncomputable def rightPair : Finger.Pair :=
  ⟨empty, .last (.one (.leaf (rebuild (fun _ => 1) child) 6)) (.base (.leaf .nil 0))⟩

private theorem emptyValid : empty.Valid 0 :=
  ⟨trivial, ⟨.leaf _ _, le_rfl⟩, fun _ => ⟨_, rfl⟩⟩
private theorem leftValid : leftPair.Valid :=
  ⟨⟨⟨.leaf _ _, by norm_num [WeightedTree.Nonnegative]⟩, ⟨.leaf _ _, le_rfl⟩,
    by intro h; cases h⟩, emptyValid⟩
private theorem rightValid : rightPair.Valid :=
  ⟨emptyValid, ⟨⟨.leaf _ _, by norm_num [WeightedTree.Nonnegative]⟩, ⟨.leaf _ _, le_rfl⟩,
    by intro h; cases h⟩⟩

-- This child is not initially exposed: the recursive root is the left leaf,
-- whereas the original source root is the middle key.
example : (Pointer.Config.mk (rebuild (fun _ => 1) child) []).key? = some 0 := by
  rw [Recursive.Results.rebuild_root_key (HeavyPath.Results.unit_positive child) (by decide)]
  norm_num [child, leaf, extract, LeftHeavy, HeavyPath.mass, extend,
    LabelledCursor.Config.erase, LabelledCursor.Frame.erase, Pointer.Config.key?,
    Pointer.offset, LabelledTree.erase, Tree.size]

-- The carry is 2 and the departing finger's weight is 7. Entering the child
-- moves its own unit weight out of the fringe, so the new pair has mass 11.
-- The intervening ancestor separator moves the arriving root to rank 2.
example : ∃ (view : Recursive.Exposure.View) (cost : Nat),
    view.Valid (fun _ => 1) (leaf 0) (leaf 2) ∧
    let next := leftPair.downLeft (view.leftTree (fun _ => 1) (leaf 0))
      (view.rightTree (fun _ => 1) (leaf 2)) 3 8
    Pointer.Trace ⟨leftPair.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
    cost + next.potential + view.potential ≤ 54 + leftPair.potential + (rootPair (fun _ => 1) child).potential ∧
    next.mass = 11 ∧ (Pointer.Config.mk next.tree []).key? = some 2 := by
  have stored : leftPair.lower.top = .leaf (rebuild (fun _ => 1) child).mirror (2 + HeavyPath.mass (fun _ => 1) child) := by
    norm_num [leftPair, Layer.top, child, leaf, HeavyPath.mass]
  obtain ⟨view, cost, viewValid, trace, valid, bound, mass, rank⟩ :=
    Transfer.Exposure.Results.downLeft_source leftValid (HeavyPath.Results.unit_positive child)
      (carry := 2) (fingerWeight := 7) (by norm_num) (by norm_num) stored
  have size : leftPair.lower.decode.tree.mirror.size = 4 := by
    change (Tree.node (rebuild (fun _ => 1) child).mirror .nil).mirror.size = 4
    simp only [Tree.mirror_size, Tree.size, Recursive.Results.rebuild_size (HeavyPath.Results.unit_positive child)]
    rfl
  norm_num [child, leaf, HeavyPath.mass] at trace valid bound mass rank
  have inputMass : leftPair.mass = 5 := by
    norm_num [Pair.mass, leftPair, empty, Layer.decode, Regulars.attach, Icing.decode, WeightedTree.mass]
  rw [inputMass] at mass
  have sizePlain : leftPair.lower.decode.tree.size = 4 := by simpa only [Tree.mirror_size] using size
  norm_num [sizePlain, LabelledTree.erase, Tree.size] at rank
  exact ⟨view, cost, viewValid, trace, valid, bound, by dsimp only [leaf]; linarith only [mass], rank⟩

-- The opposite orientation has different carry and departing-finger charges.
example : ∃ (view : Recursive.Exposure.View) (cost : Nat),
    view.Valid (fun _ => 1) (leaf 0) (leaf 2) ∧
    let next := rightPair.downRight (view.leftTree (fun _ => 1) (leaf 0))
      (view.rightTree (fun _ => 1) (leaf 2)) 10 4
    Pointer.Trace ⟨rightPair.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
    cost + next.potential + view.potential ≤ 54 + rightPair.potential + (rootPair (fun _ => 1) child).potential ∧
    next.mass = 14 ∧ (Pointer.Config.mk next.tree []).key? = some 2 := by
  have stored : rightPair.upper.top = .leaf (rebuild (fun _ => 1) child) (3 + HeavyPath.mass (fun _ => 1) child) := by
    norm_num [rightPair, Layer.top, child, leaf, HeavyPath.mass]
  obtain ⟨view, cost, viewValid, trace, valid, bound, mass, rank⟩ :=
    Transfer.Exposure.Results.downRight_source rightValid (HeavyPath.Results.unit_positive child)
      (carry := 3) (fingerWeight := 9) (by norm_num) (by norm_num) stored
  norm_num [child, leaf, HeavyPath.mass] at trace valid bound mass rank
  have inputMass : rightPair.mass = 6 := by
    norm_num [Pair.mass, rightPair, empty, Layer.decode, Regulars.attach, Icing.decode, WeightedTree.mass]
  rw [inputMass] at mass
  norm_num [rightPair, empty, Layer.decode, Regulars.attach, Icing.decode, WeightedTree.tree,
    WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror, Tree.size, LabelledTree.erase] at rank
  exact ⟨view, cost, viewValid, trace, valid, bound, by dsimp only [leaf]; linarith only [mass], rank⟩

-- A leaf exposure retains no residual heavy-path credit.
example (view : Recursive.Exposure.View) (valid : view.Valid (fun _ : Nat => (1 : ℝ)) .nil .nil) :
    view = .leaf ∧ view.potential = 0 := by
  cases view with
  | leaf => exact ⟨rfl, rfl⟩
  | left rest => exact False.elim (valid.2.1 rfl)
  | right rest => exact False.elim (valid.2.1 rfl)

end RotationBST.Tests.FingerRecursiveTransfer
