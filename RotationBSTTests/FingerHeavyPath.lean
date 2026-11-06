module

public import RotationBST.Structures.HeavyPath.Finger.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.FingerHeavyPath
open HeavyPath HeavyPath.Paired HeavyPath.Recursive LabelledCursor PopTart PopTart.WeightedTree PopTart.Chocolate

private def single (x : Nat) : LabelledTree Nat := .node .nil x .nil
private def leaf : Tree := .node .nil .nil
private def weight (x : Nat) : ℝ := x + 1
private def frames : List (Frame Nat) := [.right (single 4) 5, .left 9 (single 10), .right (single 0) 1]
private def source : LabelledTree Nat := plug frames (.node (single 6) 7 (single 8))
private noncomputable def represented : Finger.Pair := Finger.build weight frames (single 6) (single 8)

private theorem positive : Positive weight source := by
  norm_num [source, frames, plug, single, Positive, weight]

private theorem single_rebuilt (x : Nat) : rebuild weight (.node .nil x .nil) = leaf := by
  simp [rebuild, rebuildFuel, leaf, LabelledTree.erase, Tree.size, extract,
    LeftHeavy, HeavyPath.mass, Stacks.buildWith, Stacks.empty, Stacks.tree,
    Layer.decode, Regulars.attach, Icing.decode, WeightedTree.tree, WeightedTree.skeleton,
    Pointer.Lazy.Skeleton.tree, Tree.mirror]

-- Both directions occur on the source path, and both finger children survive.
-- The shifted charge of the last lower payload is 6 + 7, whereas its own
-- weight is only 7. The first outer payload has no separator charge.
example : represented.lower.decode.mirror.fringe = [(leaf, 1), (leaf, 7), (leaf, 13)] ∧
    represented.upper.decode.fringe = [(leaf, 19), (leaf, 11)] := by
  have fringes := (Finger.Results.build_valid_fringe positive).2
  norm_num [represented, frames, lowerFrames, upperFrames, Finger.sideSlots,
    framePayload, frameKey, single_rebuilt, single, HeavyPath.mass, weight] at fringes ⊢
  exact fringes

example : represented.Valid := (Finger.Results.build_valid_fringe positive).1

example : represented.mass = 51 := by
  have partition := Finger.Results.build_mass positive
  change weight 7 + represented.mass = HeavyPath.mass weight source at partition
  norm_num [weight, source, frames, plug, single, HeavyPath.mass] at partition
  linarith

example : represented.tree.size = 9 := Finger.Results.build_size positive

example : (Pointer.Config.mk represented.tree []).key? = some 5 := by
  have key := Finger.Results.build_root_key positive
  norm_num only [Config.erase, Pointer.Config.key?, frames, List.map_cons, List.map_nil,
    Frame.erase, Pointer.offset, single, LabelledTree.erase, Tree.size] at key
  exact key

private theorem ordered : source.Ordered := by
  norm_num [source, frames, plug, single, LabelledTree.Ordered, LabelledTree.inorder]

example : ∃! u : LabelledTree Nat, u.erase = represented.tree ∧
    u.inorder = [0, 1, 4, 5, 6, 7, 8, 9, 10] ∧ u.Ordered :=
  Finger.Results.build_labels positive ordered

-- Initialization is a legal physical transformation, with its linear bound
-- kept separate from the still-unproved cost of ongoing simulated updates.
example : ∃ cost, cost ≤ 144 ∧ Pointer.Trace ⟨source.erase, []⟩ ⟨represented.tree, []⟩ cost :=
  Finger.Results.build_initialization positive

-- Repeated labels and empty off-path payloads retain all separator nodes.
private def repeatedFrames : List (Frame Nat) := [.left 0 .nil, .left 0 .nil]

example : (Finger.build (fun _ : Nat => 1) repeatedFrames .nil .nil).upper.decode.fringe =
    [(.nil, 1), (.nil, 1), (.nil, 0)] := by
  have pos := HeavyPath.Results.unit_positive (plug repeatedFrames (single 0))
  have fringe := (Finger.Results.build_valid_fringe pos).2.2
  norm_num [repeatedFrames, upperFrames, Finger.sideSlots, frameKey, framePayload,
    HeavyPath.mass, rebuild, rebuildFuel, LabelledTree.erase, Tree.size] at fringe
  exact fringe

example : (Finger.build (fun _ : Nat => 1) repeatedFrames .nil .nil).tree.size = 3 :=
  Finger.Results.build_size (HeavyPath.Results.unit_positive (plug repeatedFrames (single 0)))

-- With no ancestors the current source root is retained, with independently
-- rebuilt left and right children; there is no extraneous separator.
example (l r : LabelledTree Nat) :
    (Finger.build weight [] l r).tree = .node (rebuild weight l) (rebuild weight r) := by
  simp [Finger.build, Finger.Pair.tree, lowerFrames, upperFrames, Finger.sideSlots,
    Finger.assemble, Finger.reflectSlot, Layer.decode, Regulars.attach, Icing.decode,
    WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror_mirror]

-- The full weighted theorem uses original node weights at exact ranks,
-- including a boundary payload and an upper-path separator.
example : (Tree.depth represented.tree 4 : ℝ) ≤ 15 + 15 * Real.logb 2 (59 / 7) := by
  have bound := Finger.Results.build_depth positive
    (before := [0, 1, 4, 5]) (target := 6) (after := [7, 8, 9, 10]) rfl
  norm_num [source, frames, plug, single, HeavyPath.mass, weight] at bound
  exact bound

example : (Tree.depth represented.tree 7 : ℝ) ≤ 15 + 15 * Real.logb 2 (59 / 10) := by
  have bound := Finger.Results.build_depth_at positive ⟨7, by decide⟩
  norm_num [source, frames, plug, single, HeavyPath.mass, weight, LabelledTree.inorder] at bound
  exact bound

example (rank : Fin 9) :
    (Tree.depth (Finger.build (fun _ => 1) frames (single 6) (single 8)).tree rank.val : ℝ) ≤
      15 + 15 * Real.logb 2 9 :=
  Finger.Results.build_unit_depth frames (single 6) (single 8) 7 rank.val rank.isLt

example : ∃ (visited : Pointer.Config) (cost : Nat),
    visited.tree = represented.tree ∧ visited.key? = some 7 ∧
    Pointer.Trace ⟨represented.tree, []⟩ visited cost ∧
    Pointer.Trace visited ⟨represented.tree, []⟩ cost ∧
    (1 + 2 * cost : ℝ) ≤ 31 + 30 * Real.logb 2 (59 / 10) := by
  have walk := Finger.Results.build_search_walk positive ⟨7, by decide⟩
  norm_num [source, frames, plug, single, HeavyPath.mass, weight, LabelledTree.inorder] at walk ⊢
  exact walk

example (rank : Fin 3) :
    (Tree.depth (Finger.build (fun _ : Nat => 1) repeatedFrames .nil .nil).tree rank.val : ℝ) ≤
      15 + 15 * Real.logb 2 3 :=
  Finger.Results.build_unit_depth repeatedFrames .nil .nil 0 rank.val rank.isLt

-- A finger can follow a light edge, leaving almost all weight in one outer
-- payload. Applying the heavy-path half-mass premise here would be wrong.
private def heavyPayload : LabelledTree Nat := .node (single 2) 3 (single 4)
private def heavyFrames : List (Frame Nat) := [.left 1 heavyPayload]
private def heavySource : LabelledTree Nat := plug heavyFrames (single 0)
private def heavyWeight (x : Nat) : ℝ := if x = 3 then 1000 else 1

private theorem heavyPositive : Positive heavyWeight heavySource := by
  norm_num [heavySource, heavyFrames, plug, heavyPayload, single, Positive, heavyWeight]

example : HeavyPath.mass heavyWeight heavySource < 2 * HeavyPath.mass heavyWeight heavyPayload := by
  norm_num [heavySource, heavyFrames, plug, heavyPayload, single, HeavyPath.mass, heavyWeight]

example : ¬ SolidContext heavyWeight (single 0) heavyFrames := by
  norm_num [SolidContext, heavyFrames, LeftHeavy, heavyPayload, single, HeavyPath.mass, heavyWeight]

example : (Tree.depth (Finger.build heavyWeight heavyFrames .nil .nil).tree 3 : ℝ) ≤
    15 + 15 * Real.logb 2 (1004 / 1000) := by
  have bound := Finger.Results.build_depth heavyPositive
    (before := [0, 1, 2]) (target := 3) (after := [4]) rfl
  norm_num [heavySource, heavyFrames, plug, heavyPayload, single, HeavyPath.mass, heavyWeight] at bound ⊢
  exact bound

end RotationBST.Tests.FingerHeavyPath
