module

public import RotationBST.Structures.HeavyPath.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.HeavyPath
open RotationBST.HeavyPath LabelledCursor

private def single (x : Nat) : LabelledTree Nat := .node .nil x .nil
private def twig : LabelledTree Nat := .node (single 4) 5 .nil
private def middle : LabelledTree Nat := .node (single 2) 3 twig
private def branch : LabelledTree Nat := .node middle 6 (single 7)
private def zigzag : LabelledTree Nat := .node (single 0) 1 branch
private def unitWeight : Nat → ℝ := fun _ => 1
private def frames : List (Frame Nat) :=
  [.left 5 .nil, .right (single 2) 3, .left 6 (single 7), .right (single 0) 1]

-- Four solid edges alternate directions. Frames keep every off-path subtree.
private theorem zigzagExtract : extract unitWeight zigzag = ⟨single 4, frames⟩ := by
  norm_num [extract, LeftHeavy, mass, extend, zigzag, branch, middle, twig,
    single, unitWeight, frames]

example : (extract unitWeight zigzag).tree = zigzag := Results.extract_tree _ _

example : Pointer.Trace ⟨zigzag.erase, []⟩
    (Config.erase ⟨single 4, frames⟩) 4 := by
  have trace := Results.extract_trace unitWeight (show zigzag ≠ .nil by decide)
  simpa only [zigzagExtract, frames, List.length_cons, List.length_nil] using trace

-- Endpoint-to-root lower separators decrease; upper separators increase.
example : lowerKeys frames = [3, 1] ∧ upperKeys frames = [5, 6] := by
  exact ⟨rfl, rfl⟩

private theorem zigzagOrdered : zigzag.Ordered := by
  norm_num [zigzag, branch, middle, twig, single, LabelledTree.Ordered,
    LabelledTree.inorder]

example : (lowerKeys frames).Pairwise (fun a b => b < a) ∧
    (upperKeys frames).Pairwise (fun a b => a < b) ∧
    (∀ x ∈ lowerKeys frames, x < 4) ∧ (∀ x ∈ upperKeys frames, 4 < x) := by
  have ordered := Results.extract_order unitWeight zigzagOrdered
  rw [zigzagExtract] at ordered
  exact ⟨ordered.1, ordered.2.1, ordered.2.2 4 (by simp [single, LabelledTree.inorder])⟩

example : frames.map (frameMass unitWeight) = [1, 2, 2, 2] := by
  norm_num [frames, frameMass, mass, single, unitWeight]

example : mass unitWeight zigzag = 1 + (frames.map (frameMass unitWeight)).sum := by
  have partition := Results.extract_mass unitWeight zigzag
  simpa only [zigzagExtract, single, mass, unitWeight, zero_add, add_zero] using partition

example : ∀ frame ∈ frames, 0 < frameMass unitWeight frame := by
  have positive := Results.extract_positive
    (show Positive unitWeight zigzag from Results.unit_positive zigzag)
  rw [zigzagExtract] at positive
  exact positive.2

-- The target 2 uses one light edge, then two solid edges on the way to root.
private theorem pathTwo : Path unitWeight zigzag 2 1 3 := by
  apply Path.rightSolid
  · apply Path.leftSolid
    · apply Path.leftLight (Path.root .nil .nil 2)
      norm_num [LeftHeavy, mass, single, twig, unitWeight]
    · norm_num [LeftHeavy, mass, single, middle, twig, unitWeight]
  · norm_num [LeftHeavy, mass, single, branch, middle, twig, unitWeight]

example : (1 : ℝ) ≤ Real.logb 2 8 := by
  have bound := Results.unit_light_bound pathTwo
  simpa [zigzag, branch, middle, twig, single, LabelledTree.erase, Tree.size] using bound

-- Equal child masses choose left; the right edge is then light.
private def tied : LabelledTree Nat := .node (single 0) 1 (single 2)

example : extract unitWeight tied = ⟨single 0, [.left 1 (single 2)]⟩ := by
  norm_num [extract, tied, single, LeftHeavy, mass, unitWeight, extend]

private theorem tiedRight : Path unitWeight tied 2 1 1 := by
  apply Path.rightLight (Path.root .nil .nil 2)
  norm_num [LeftHeavy, single, mass, unitWeight]

example : (1 : ℝ) ≤ Real.logb 2 3 := by
  have bound := Results.unit_light_bound tiedRight
  simpa [tied, single, LabelledTree.erase, Tree.size] using bound

-- Changing analysis weights changes the selected path without changing keys.
private def weighted : Nat → ℝ := fun x => if x = 2 then 4 else 1

example : extract weighted tied = ⟨single 2, [.right (single 0) 1]⟩ := by
  norm_num [extract, tied, single, LeftHeavy, mass, weighted, extend]

-- A nonempty zero-mass sibling must survive an empty-child tie.
private def zeroTree : LabelledTree Nat := .node .nil 0 (single 1)
private def zeroWeight : Nat → ℝ := fun x => if x = 0 then 1 else 0

example : extract zeroWeight zeroTree = ⟨zeroTree, []⟩ := by
  norm_num [extract, zeroTree, single, LeftHeavy, mass, zeroWeight]

example : Nonnegative zeroWeight zeroTree ∧ ¬ Positive zeroWeight zeroTree := by
  norm_num [Nonnegative, Positive, zeroTree, single, zeroWeight]

example : extract unitWeight (.nil : LabelledTree Nat) = ⟨.nil, []⟩ := rfl

example : ∃ x, (extract unitWeight (single 9)).focus = .node .nil x .nil ∧
    Path unitWeight (single 9) x 0 (extract unitWeight (single 9)).context.length :=
  Results.extract_path (Results.unit_positive _) (by decide)

end RotationBST.Tests.HeavyPath
