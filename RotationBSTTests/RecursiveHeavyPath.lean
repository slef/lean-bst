module

public import RotationBST.Structures.HeavyPath.Recursive.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.RecursiveHeavyPath
open HeavyPath HeavyPath.Paired HeavyPath.Recursive LabelledCursor

private def single (x : Nat) : LabelledTree Nat := .node .nil x .nil
private def twig : LabelledTree Nat := .node (single 6) 7 .nil
private def frames : List (Frame Nat) := [.left 1 .nil, .left 2 .nil, .left 5 twig]
private def original : LabelledTree Nat := plug frames (single 0)
private def unitWeight : Nat → ℝ := fun _ => 1

private theorem twigRebuilt : rebuild unitWeight twig = .node .nil (.node .nil .nil) := by
  norm_num [rebuild, rebuildFuel, twig, single, LabelledTree.erase, Tree.size,
    extract, LeftHeavy, mass, unitWeight, extend, Stacks.buildWith, Stacks.pushWith,
    Stacks.empty, Stacks.tree, PopTart.Chocolate.Layer.push, PopTart.Chocolate.Layer.decode,
    PopTart.Chocolate.Regulars.attach, PopTart.Chocolate.Icing.decode,
    PopTart.WeightedTree.tree, PopTart.WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror]

private theorem extracted : extract unitWeight original = ⟨single 0, frames⟩ := by
  norm_num [original, plug, frames, twig, single, extract, LeftHeavy, mass, unitWeight, extend]

-- The upper off-path twig is recursively changed from a left chain to a
-- right chain. The single-path constructor alone would retain its old shape.
example : rebuild unitWeight twig ≠ twig.erase := by rw [twigRebuilt]; decide

example : rebuild unitWeight original =
    .node .nil (.node (.node (.node .nil .nil) .nil) (.node .nil (.node .nil .nil))) := by
  rw [Recursive.Results.rebuild_eq
    (show Positive unitWeight original from HeavyPath.Results.unit_positive original) (by decide), extracted]
  simp only [frames, Stacks.buildWith, Stacks.pushWith]
  rw [twigRebuilt]
  norm_num [Stacks.empty, Stacks.tree,
    PopTart.Chocolate.Layer.push, PopTart.Chocolate.Layer.decode,
    PopTart.Chocolate.Regulars.attach, PopTart.Chocolate.Icing.decode,
    PopTart.WeightedTree.tree, PopTart.WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree,
    Tree.mirror, rebuild, rebuildFuel, LabelledTree.erase,
    Tree.size, unitWeight, mass, twig, single]

example : Layout unitWeight original (rebuild unitWeight original) :=
  Recursive.Results.rebuild_layout (HeavyPath.Results.unit_positive original)

example : (rebuild unitWeight original).size = 6 := by
  simpa [original, plug, frames, single, twig, LabelledTree.erase, Tree.size] using
    Recursive.Results.rebuild_size (show Positive unitWeight original from HeavyPath.Results.unit_positive original)

-- Extra recursion budget cannot change the canonical result.
example : rebuildFuel unitWeight 100 original = rebuild unitWeight original :=
  Recursive.Results.rebuildFuel_eq 100 (HeavyPath.Results.unit_positive original) (by decide)

example : rebuildFuel unitWeight 0 twig = twig.erase := rfl

-- The symmetric case has a nonzero endpoint rank and a recursively rebuilt
-- lower payload. Payload size preservation is needed for the rank equation.
private def lowerTwig : LabelledTree Nat := .node (single 0) 1 .nil
private def lowerOriginal : LabelledTree Nat :=
  .node lowerTwig 2 (.node .nil 7 (.node .nil 8 (single 9)))

example : (Pointer.Config.mk (rebuild unitWeight lowerOriginal) []).key? = some 5 := by
  rw [Recursive.Results.rebuild_root_key
    (show Positive unitWeight lowerOriginal from HeavyPath.Results.unit_positive lowerOriginal) (by decide)]
  norm_num [lowerOriginal, lowerTwig, single, extract, LeftHeavy, mass, unitWeight,
    extend, Config.erase, Pointer.Config.key?, Pointer.offset, Frame.erase,
    LabelledTree.erase, Tree.size]

-- Nonuniform weights change the top path. Charges still use those original
-- node weights even though every payload is recursively restructured.
private def weighted : Nat → ℝ := fun x => if x = 7 then 5 else 1

example : (rebuild weighted original).size = 6 := by
  have positive : Positive weighted original := by
    norm_num [Positive, weighted, original, plug, frames, twig, single]
  simpa [original, plug, frames, twig, single, LabelledTree.erase, Tree.size] using
    Recursive.Results.rebuild_size positive

example : (Pointer.Config.mk (rebuild weighted original) []).key? = some 4 := by
  have positive : Positive weighted original := by
    norm_num [Positive, weighted, original, plug, frames, twig, single]
  rw [Recursive.Results.rebuild_root_key positive (by decide)]
  norm_num [original, plug, frames, twig, single, extract, LeftHeavy, mass, weighted,
    extend, Config.erase, Pointer.Config.key?, Pointer.offset, Frame.erase,
    LabelledTree.erase, Tree.size]

private theorem ordered : original.Ordered := by
  norm_num [original, plug, frames, single, twig, LabelledTree.Ordered, LabelledTree.inorder]

example : ∃! u : LabelledTree Nat,
    u.erase = rebuild unitWeight original ∧ u.inorder = [0, 1, 2, 5, 6, 7] ∧ u.Ordered := by
  simpa [original, plug, frames, single, twig, LabelledTree.inorder] using
    Recursive.Results.rebuild_labels
      (show Positive unitWeight original from HeavyPath.Results.unit_positive original) ordered

example : ∃ cost, cost ≤ 96 ∧
    Pointer.Trace ⟨original.erase, []⟩ ⟨rebuild unitWeight original, []⟩ cost := by
  simpa [original, plug, frames, single, twig, LabelledTree.erase, Tree.size] using
    Recursive.Results.rebuild_initialization
      (show Positive unitWeight original from HeavyPath.Results.unit_positive original)

-- Both the physical payload and its original separator-plus-subtree charge
-- survive recursive substitution and the upper-stack reflection.
example :
    (Stacks.buildWith unitWeight (rebuild unitWeight) frames Stacks.empty).upper.decode.mirror.fringe =
      [(.nil, 0), (.nil, 1), (.nil, 1), (.node .nil (.node .nil .nil), 3)] := by
  obtain ⟨endpoint, focus, tree, valid, partition, lower, upper⟩ :=
    Recursive.Results.rebuild_pair
      (show Positive unitWeight original from HeavyPath.Results.unit_positive original) (by decide)
  rw [extracted] at upper
  simp only [upperSlotsWith, frames] at upper
  rw [twigRebuilt] at upper
  norm_num [unitWeight, mass, twig, single,
    rebuild, rebuildFuel, LabelledTree.erase, Tree.size] at upper
  simpa only [frames, twig, single] using upper

example : rebuild unitWeight (.nil : LabelledTree Nat) = .nil := rfl
example : rebuild unitWeight (single 8) = .node .nil .nil := by
  norm_num [rebuild, rebuildFuel, single, LabelledTree.erase, Tree.size, extract,
    LeftHeavy, mass, unitWeight, Stacks.buildWith, Stacks.empty, Stacks.tree,
    PopTart.Chocolate.Layer.decode, PopTart.Chocolate.Regulars.attach,
    PopTart.Chocolate.Icing.decode, PopTart.WeightedTree.tree, PopTart.WeightedTree.skeleton,
    Pointer.Lazy.Skeleton.tree, Tree.mirror]

-- Public completeness requires positive weights. A zero-weight, non-leaf
-- endpoint takes the explicit fallback and retains the whole source shape.
example : rebuild (fun _ : Nat => (0 : ℝ)) (.node .nil 0 (single 1)) =
    (.node .nil 0 (single 1) : LabelledTree Nat).erase := by
  norm_num [rebuild, rebuildFuel, single, LabelledTree.erase, Tree.size, extract, LeftHeavy, mass]

end RotationBST.Tests.RecursiveHeavyPath
