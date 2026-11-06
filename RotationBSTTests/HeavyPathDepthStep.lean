module

public import RotationBST.Structures.HeavyPath.Recursive.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.HeavyPathDepthStep
open HeavyPath HeavyPath.Paired HeavyPath.Recursive PopTart PopTart.WeightedTree LabelledCursor

private def single (x : Nat) : LabelledTree Nat := .node .nil x .nil
private def twig : LabelledTree Nat := .node (single 6) 7 .nil
private def frame : Frame Nat := .left 5 twig
private def frames : List (Frame Nat) := [.left 1 .nil, .left 2 .nil, frame]
private def original : LabelledTree Nat := plug frames (single 0)
private def unitWeight : Nat → ℝ := fun _ => 1
private theorem positive : Positive unitWeight original := HeavyPath.Results.unit_positive original

private theorem extracted : extract unitWeight original = ⟨single 0, frames⟩ := by
  norm_num [original, plug, frames, frame, twig, single, extract, LeftHeavy, HeavyPath.mass, unitWeight, extend]

private theorem member : frame ∈ (extract unitWeight original).context := by
  rw [extracted]; simp [frames]

private theorem twigRebuilt : rebuild unitWeight twig = .node .nil (.node .nil .nil) := by
  norm_num [rebuild, rebuildFuel, twig, single, LabelledTree.erase, Tree.size,
    extract, LeftHeavy, HeavyPath.mass, unitWeight, extend, Stacks.buildWith, Stacks.pushWith,
    Stacks.empty, Stacks.tree, Chocolate.Layer.push, Chocolate.Layer.decode,
    Chocolate.Regulars.attach, Chocolate.Icing.decode, WeightedTree.tree,
    WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror]

private theorem occurrence :
    LocatedSlot (.node (rootPair unitWeight original).lower.decode (rootPair unitWeight original).upper.decode.mirror)
      (rebuild unitWeight (framePayload frame)) (frameMass unitWeight frame) 4 2 := by
  unfold rootPair
  rw [extracted]
  simp only [frames, frame, framePayload, Stacks.buildWith, Stacks.pushWith]
  rw [twigRebuilt]
  norm_num [frameMass, unitWeight, HeavyPath.mass, twig, single, Stacks.empty,
    Chocolate.Layer.push, Chocolate.Layer.decode, Chocolate.Regulars.attach, Chocolate.Icing.decode,
    WeightedTree.mirror, rebuild, rebuildFuel, LabelledTree.erase, Tree.size]
  exact .right (.right (.leaf _ _))

-- The payload has mass 2 in a source of mass 6, while its slot charge is 3.
example : 2 * HeavyPath.mass unitWeight twig ≤ HeavyPath.mass unitWeight original :=
  Recursive.Results.extract_payload_half positive member

example : 0 < unitWeight (frameKey frame) ∧
    unitWeight (frameKey frame) ≤ frameMass unitWeight frame ∧
    HeavyPath.mass unitWeight twig ≤ frameMass unitWeight frame :=
  Recursive.Results.extract_charge_bounds positive member

-- The recursive step reaches key 7 at local rank 1, hence global rank 5.
example : (Tree.depth (rebuild unitWeight original) 5 : ℝ) ≤ 7 + 15 * Real.logb 2 6 := by
  have childBound : (Tree.depth (rebuild unitWeight (framePayload frame)) 1 : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass unitWeight (framePayload frame) / 1) := by
    change (Tree.depth (rebuild unitWeight twig) 1 : ℝ) ≤ _
    rw [twigRebuilt]
    norm_num [Tree.depth, Tree.size, frame, framePayload, twig, single, HeavyPath.mass, unitWeight]
  have bound := Recursive.Results.payload_depth_step positive (by decide) member occurrence
    (x := 1) (keyWeight := 1)
    (by change 1 < (rebuild unitWeight twig).size; rw [twigRebuilt]; decide)
    (by norm_num) (by norm_num [frame, framePayload, twig, single, HeavyPath.mass, unitWeight]) childBound
  norm_num [original, plug, frames, frame, twig, single, HeavyPath.mass, unitWeight] at bound
  exact bound

-- The separator just before this same physical occurrence is original key 5
-- at rank 3. It is bounded without applying a recursive hypothesis to a key.
example : (Tree.depth (rebuild unitWeight original) 3 : ℝ) ≤ 7 + 15 * Real.logb 2 6 := by
  have bound := Recursive.Results.predecessor_depth_step positive (by decide) member occurrence (by decide)
  norm_num [original, plug, frames, frame, twig, single, HeavyPath.mass, unitWeight, frameKey] at bound
  exact bound

private def lowerTwig : LabelledTree Nat := .node (single 0) 1 .nil
private def lowerFrame : Frame Nat := .right lowerTwig 2
private def lowerFrames : List (Frame Nat) := [.right .nil 8, .right .nil 7, lowerFrame]
private def lowerOriginal : LabelledTree Nat := plug lowerFrames (single 9)

private theorem lowerExtracted : extract unitWeight lowerOriginal = ⟨single 9, lowerFrames⟩ := by
  norm_num [lowerOriginal, plug, lowerFrames, lowerFrame, lowerTwig, single,
    extract, LeftHeavy, HeavyPath.mass, unitWeight, extend]

private theorem lowerRebuilt : rebuild unitWeight lowerTwig = .node .nil (.node .nil .nil) := by
  norm_num [rebuild, rebuildFuel, lowerTwig, single, LabelledTree.erase, Tree.size,
    extract, LeftHeavy, HeavyPath.mass, unitWeight, extend, Stacks.buildWith, Stacks.pushWith,
    Stacks.empty, Stacks.tree, Chocolate.Layer.push, Chocolate.Layer.decode,
    Chocolate.Regulars.attach, Chocolate.Icing.decode, WeightedTree.tree,
    WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror]

private theorem lowerOccurrence :
    LocatedSlot (.node (rootPair unitWeight lowerOriginal).lower.decode
      (rootPair unitWeight lowerOriginal).upper.decode.mirror)
      (rebuild unitWeight (framePayload lowerFrame)) (frameMass unitWeight lowerFrame) 0 2 := by
  unfold rootPair
  rw [lowerExtracted]
  simp only [lowerFrames, lowerFrame, framePayload, Stacks.buildWith, Stacks.pushWith]
  rw [lowerRebuilt]
  norm_num [frameMass, unitWeight, HeavyPath.mass, lowerTwig, single, Stacks.empty,
    Chocolate.Layer.push, Chocolate.Layer.decode, Chocolate.Regulars.attach, Chocolate.Icing.decode,
    WeightedTree.mirror, rebuild, rebuildFuel, LabelledTree.erase, Tree.size]
  exact .left (.left (.leaf _ _))

-- The lower orientation charges the successor separator, here original key 2.
example : (Tree.depth (rebuild unitWeight lowerOriginal) 2 : ℝ) ≤ 7 + 15 * Real.logb 2 6 := by
  have sourcePositive : Positive unitWeight lowerOriginal := HeavyPath.Results.unit_positive lowerOriginal
  have member : lowerFrame ∈ (extract unitWeight lowerOriginal).context := by
    rw [lowerExtracted]; simp [lowerFrames]
  have existsKey : 0 + (rebuild unitWeight (framePayload lowerFrame)).size <
      (rebuild unitWeight lowerOriginal).size := by
    rw [Recursive.Results.rebuild_size sourcePositive]
    change 0 + (rebuild unitWeight lowerTwig).size < _
    rw [lowerRebuilt]
    decide
  have bound := Recursive.Results.successor_depth_step sourcePositive (by decide) member lowerOccurrence existsKey
  change (Tree.depth (rebuild unitWeight lowerOriginal) (0 + (rebuild unitWeight lowerTwig).size) : ℝ) ≤ _ at bound
  rw [lowerRebuilt] at bound
  norm_num [lowerOriginal, plug, lowerFrames, lowerFrame, lowerTwig, single,
    HeavyPath.mass, unitWeight, frameKey, Tree.size] at bound
  exact bound

-- A crossing with exactly half the mass is the tight additive-cost case.
example {d : ℝ} (bound : d ≤ 8 + 7 * Real.logb 2 (8 / 4) + (7 + 15 * Real.logb 2 (4 / 1))) :
    d ≤ 7 + 15 * Real.logb 2 (8 / 1) :=
  Recursive.Results.depth_telescope (by norm_num) (by norm_num) (by norm_num) bound

end RotationBST.Tests.HeavyPathDepthStep
