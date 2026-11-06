module

public import RotationBST.Structures.HeavyPath.Recursive.Exposure.Abstract
public import RotationBST.Structures.HeavyPath.Finger.Transfer.Exposure.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.HeavyPathExposure
open HeavyPath HeavyPath.Paired HeavyPath.Recursive LabelledCursor
open PopTart PopTart.WeightedTree PopTart.Chocolate

private def leaf (x : Nat) : LabelledTree Nat := .node .nil x .nil
private def leftSubtree : LabelledTree Nat := .node (leaf 0) 1 (leaf 2)
private def source : LabelledTree Nat := .node leftSubtree 3 (leaf 4)

-- The initial recursive representation has the heavy-path endpoint at rank
-- zero; source-root exposure must instead recover the node at rank three.
example : (Pointer.Config.mk (rebuild (fun _ => 1) source) []).key? = some 0 := by
  rw [Recursive.Results.rebuild_root_key (HeavyPath.Results.unit_positive source) (by decide)]
  norm_num [source, leftSubtree, leaf, extract, LeftHeavy, HeavyPath.mass, extend,
    Config.erase, Frame.erase, Pointer.Config.key?, Pointer.offset, LabelledTree.erase, Tree.size]

example : ∃ a b cost credit,
    Pointer.Trace ⟨rebuild (fun _ => 1) source, []⟩ ⟨.node a b, []⟩ cost ∧
    a.size = 3 ∧ b.size = 1 ∧
    (Pointer.Config.mk (.node a b) []).key? = some 3 ∧
    cost + credit ≤ 24 + (rootPair (fun _ => 1) source).potential :=
  Recursive.Exposure.Results.root_exposure (HeavyPath.Results.unit_positive source)

-- A nonuniform right-heavy example exercises the opposite physical rotation.
private def weightedSource : LabelledTree Nat := .node (leaf 0) 1 (.node (leaf 2) 3 (leaf 4))
private def weight (x : Nat) : ℝ := x + 1
private theorem weightedPositive : Positive weight weightedSource := by
  norm_num [weightedSource, leaf, Positive, weight]

example : ∃ rest : Stacks,
    rest.Represents weight (rebuild weight) (extract weight (.node (leaf 2) 3 (leaf 4))).context ∧
    Pointer.Trace ⟨rebuild weight weightedSource, []⟩ ⟨.node (rebuild weight (leaf 0)) rest.tree, []⟩
      ((rootPair weight weightedSource).exposeCost (.right (leaf 0) 1)) ∧
    (rootPair weight weightedSource).exposeCost (.right (leaf 0) 1) + rest.potential ≤
      24 + (rootPair weight weightedSource).potential ∧
    rest.tree.size = 3 ∧ (rootPair weight weightedSource).mass = rest.mass + 3 := by
  have exposed := Recursive.Exposure.Results.expose_right weightedPositive
    (by norm_num [LeftHeavy, HeavyPath.mass, leaf, weight]) (by decide)
  norm_num [HeavyPath.mass, leaf, weight, LabelledTree.erase, Tree.size] at exposed
  exact exposed

-- A leaf source requires no stack separator or rotation.
example : ∃ a b cost credit,
    Pointer.Trace ⟨rebuild (fun _ => 1) (leaf 9), []⟩ ⟨.node a b, []⟩ cost ∧
    a.size = 0 ∧ b.size = 0 ∧ (Pointer.Config.mk (.node a b) []).key? = some 0 ∧
    cost + credit ≤ 24 + (rootPair (fun _ => 1) (leaf 9)).potential :=
  Recursive.Exposure.Results.root_exposure (HeavyPath.Results.unit_positive (leaf 9))

private def slot : WeightedTree := .leaf .nil 1
private def frozenLayer : Layer := .last (.one slot) (.solid (.node slot slot) (.base (.leaf .nil 0)))
private def frozenPair : Stacks := ⟨frozenLayer, Stacks.empty.upper⟩
private def remaining : Stacks := ⟨.last (.two slot slot) (.base (.leaf .nil 0)), Stacks.empty.upper⟩
private def frame : Frame Nat := .right .nil 1

private theorem frozenValid : frozenLayer.Valid 0 := by
  refine ⟨⟨.leaf _ _, by norm_num [slot, WeightedTree.Nonnegative]⟩,
    ⟨.node (.leaf _ _) (.leaf _ _), ?_, ⟨.leaf _ _, le_rfl⟩, ?_⟩, ?_⟩
  all_goals norm_num [slot, WeightedTree.Nonnegative, WeightedTree.mass, Icing.decode]

private theorem frozenRepresents : frozenPair.Represents (fun _ => 1) LabelledTree.erase [frame, frame, frame] :=
by
  refine ⟨⟨frozenValid, Paired.Results.empty_valid.2⟩, ?_, rfl⟩
  norm_num [frozenPair, frozenLayer, slot, Layer.decode, Regulars.attach, Icing.decode,
    WeightedTree.fringe, lowerSlotsWith, frame, HeavyPath.mass, LabelledTree.erase]

-- The invariant includes histories whose shape differs from fresh assembly.
example : frozenPair.tree ≠ (Stacks.buildWith (fun _ => 1) LabelledTree.erase
    [frame, frame, frame] Stacks.empty).tree := by
  simp [frozenPair, frozenLayer, slot, Stacks.tree, Stacks.buildWith, Stacks.pushWith,
    frame, Stacks.empty, Layer.push, Layer.decode, Icing.decode, Regulars.attach,
    WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree]

-- Exposure thaws the icing, charges all eight pointer instructions, and
-- retains exactly the two remaining frames.
example : Pointer.Trace ⟨frozenPair.tree, []⟩ ⟨.node .nil remaining.tree, []⟩ 8 :=
  Paired.Exposure.Results.lower_trace (p := frozenPair) (crumb := slot) (rest := remaining.lower) rfl

example : ∃ rest : Stacks,
    rest.Represents (fun _ => 1) LabelledTree.erase [frame, frame] ∧
    Pointer.Trace ⟨frozenPair.tree, []⟩ ⟨.node .nil rest.tree, []⟩ 8 ∧
    8 + rest.potential ≤ 24 + frozenPair.potential ∧ frozenPair.mass = rest.mass + 1 :=
by
  have result := Paired.Exposure.Results.expose_frame (cs := [frame, frame]) (frame := frame) frozenRepresents
  simpa only [Stacks.exposeCost, frame, replaceFrame, LabelledTree.erase, Pointer.plug,
    frameMass, HeavyPath.mass, zero_add, show frozenPair.lower.popCost + 4 = 8 from rfl] using result

-- Identical payloads and equal labels retain separate fringe occurrences.
example : remaining.Represents (fun _ => 1) LabelledTree.erase [frame, frame] := by
  refine ⟨⟨?_, Paired.Results.empty_valid.2⟩, ?_, rfl⟩
  swap
  · norm_num [remaining, slot, Layer.decode, Regulars.attach, Icing.decode,
      WeightedTree.fringe, lowerSlotsWith, frame, HeavyPath.mass, LabelledTree.erase]
  refine ⟨⟨⟨.leaf _ _, ?_⟩, ⟨.leaf _ _, ?_⟩⟩, ⟨.leaf _ _, le_rfl⟩, ?_⟩
  all_goals norm_num [slot, WeightedTree.Nonnegative]

private def chain : LabelledTree Nat :=
  .node .nil 1 (.node .nil 1 (.node .nil 1 (leaf 1)))

private theorem frozenSource : frozenPair.Represents (fun _ => 1) (rebuild (fun _ => 1))
    (extract (fun _ => 1) chain).context := by
  refine ⟨⟨frozenValid, Paired.Results.empty_valid.2⟩, ?_, ?_⟩
  all_goals norm_num [chain, leaf, extract, LeftHeavy, HeavyPath.mass, extend,
    lowerSlotsWith, upperSlotsWith, rebuild, rebuildFuel, frame, frozenPair, frozenLayer,
    slot, Stacks.empty, Layer.decode, Icing.decode, Regulars.attach, WeightedTree.fringe,
    Tree.mirror, LabelledTree.erase, Tree.size]

private def enclosing : Finger.Pair :=
  ⟨.last .zero (.base (.leaf frozenPair.tree.mirror 4)), Stacks.empty.upper⟩
private theorem enclosingValid : enclosing.Valid :=
  ⟨⟨trivial, ⟨.leaf _ _, by norm_num [WeightedTree.Nonnegative]⟩,
    fun _ => ⟨_, rfl⟩⟩, Paired.Results.empty_valid.2⟩

-- An actual noncanonical frozen child can be exposed and entered inside an
-- inverted pair; the residual path, its potential, and source rank survive.
example : ∃ (view : Recursive.Exposure.View) (cost : Nat),
    view.Valid (fun _ => 1) .nil (.node .nil 1 (.node .nil 1 (leaf 1))) ∧
    let next := enclosing.downLeft (view.leftTree (fun _ : Nat => 1) .nil)
      (view.rightTree (fun _ => 1) (.node .nil 1 (.node .nil 1 (leaf 1)))) 0 10
    Pointer.Trace ⟨enclosing.tree, []⟩ ⟨next.tree, []⟩ cost ∧ next.Valid ∧
    cost + next.potential + view.potential ≤ 54 + enclosing.potential + frozenPair.potential ∧
    next.mass + 4 = enclosing.mass + 0 + 10 ∧
    (Pointer.Config.mk next.tree []).key? = some 0 := by
  have result := Finger.Transfer.Exposure.Results.downLeft_pair enclosingValid
    (HeavyPath.Results.unit_positive chain) frozenSource (oldCharge := 4) rfl
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 10)
  simpa only [chain, enclosing, frozenPair, frozenLayer, slot, Stacks.tree, Stacks.empty,
    Layer.decode, Regulars.attach, Icing.decode, WeightedTree.tree, WeightedTree.skeleton,
    Pointer.Lazy.Skeleton.tree, Tree.mirror_size, Tree.size, LabelledTree.erase, leaf,
    Nat.reduceAdd, Nat.reduceSub] using result

end RotationBST.Tests.HeavyPathExposure
