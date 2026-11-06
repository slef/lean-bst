module

public import RotationBST.Structures.HeavyPath.Paired.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.PairedHeavyPath
open HeavyPath HeavyPath.Paired PopTart PopTart.Chocolate LabelledCursor

private def single (x : Nat) : LabelledTree Nat := .node .nil x .nil
private def payload : LabelledTree Nat := .node (single 11) 12 .nil
private def frames : List (Frame Nat) :=
  [.left 5 (single 6), .right (single 2) 3, .left 9 payload]
private def original : LabelledTree Nat := plug frames (single 4)
private def unitWeight : Nat → ℝ := fun _ => 1
private noncomputable def pair : Stacks := Stacks.build unitWeight frames Stacks.empty

private theorem charges : ∀ frame ∈ frames, 0 ≤ frameMass unitWeight frame := by
  norm_num [frames, frameMass, mass, unitWeight, single, payload]

private theorem valid : pair.Valid := Results.build_valid frames Results.empty_valid charges

-- The asymmetric payload detects accidental reflection inside an upper slot.
example : payload.erase.mirror ≠ payload.erase := by decide

example : pair.lower.decode.fringe = [(single 2 |>.erase, 2), (.nil, 0)] ∧
    pair.upper.decode.mirror.fringe = [(.nil, 0), (single 6 |>.erase, 2), (payload.erase, 3)] := by
  have fringe := Results.empty_build_fringe frames charges
  norm_num [pair, frames, lowerSlots, upperSlots, single, payload, mass, unitWeight] at fringe ⊢
  exact fringe

example : pair.mass = 7 := by
  have partition := Results.build_mass frames Results.empty_valid charges
  norm_num [pair, frames, frameMass, mass, single, payload, unitWeight,
    Stacks.empty, Stacks.mass, Layer.decode, Regulars.attach, Icing.decode, WeightedTree.mass] at partition ⊢
  exact partition

private theorem extracted : extract unitWeight original = ⟨single 4, frames⟩ := by
  norm_num [original, plug, frames, single, payload, extract, LeftHeavy, mass, unitWeight, extend]

example : ∃ cost, Pointer.Trace ⟨original.erase, []⟩ ⟨pair.tree, []⟩ cost ∧
    cost + pair.potential ≤ 72 ∧ (Pointer.Config.mk pair.tree []).key? = some 2 := by
  obtain ⟨x, cost, focus, validity, partition, trace, bound, key⟩ :=
    Results.extract_build (show Positive unitWeight original from HeavyPath.Results.unit_positive original)
      (by decide : original ≠ .nil)
  refine ⟨cost, ?_, ?_, ?_⟩
  · simpa only [extracted, pair] using trace
  · simpa only [extracted, frames, List.length_cons, List.length_nil, pair] using bound
  · simpa [extracted, Config.erase, Pointer.Config.key?, Pointer.offset,
      Frame.erase, frames, single, LabelledTree.erase, Tree.size, pair] using key

-- Both payloads can be accessed from the endpoint root without opening them.
private theorem lowerSlot : WeightedTree.SlotAt pair.lower.decode (single 2).erase 2 1 := by
  norm_num [pair, Stacks.build, Stacks.push, Stacks.empty, frames, Layer.push,
    Layer.decode, Regulars.attach, Icing.decode, unitWeight, mass, single]
  exact .left (.leaf _ _)

private theorem upperSlot : WeightedTree.SlotAt pair.upper.decode.mirror payload.erase 3 1 := by
  norm_num [pair, Stacks.build, Stacks.push, Stacks.empty, frames, Layer.push,
    Layer.decode, Regulars.attach, Icing.decode, unitWeight, mass, single,
    payload, WeightedTree.mirror]
  exact .right (.leaf _ _)

example : ∃ cs : List Pointer.Frame, cs.length = 2 ∧ Pointer.plug cs payload.erase = pair.tree ∧
    Pointer.Trace ⟨pair.tree, []⟩ ⟨payload.erase, cs⟩ 2 ∧
    (2 : ℝ) ≤ 8 + 7 * Real.logb 2 (pair.mass / 3) := by
  simpa only [show 1 + 1 = 2 from rfl, Nat.cast_ofNat] using
    Results.upper_access valid upperSlot (by norm_num) (by decide)

example : ∃ cs : List Pointer.Frame, cs.length = 2 ∧ Pointer.plug cs (single 2).erase = pair.tree ∧
    Pointer.Trace ⟨pair.tree, []⟩ ⟨(single 2).erase, cs⟩ 2 ∧
    (2 : ℝ) ≤ 8 + 7 * Real.logb 2 (pair.mass / 2) := by
  simpa only [show 1 + 1 = 2 from rfl, Nat.cast_ofNat] using
    Results.lower_access valid lowerSlot (by norm_num) (by decide)

private theorem originalOrdered : original.Ordered := by
  norm_num [original, plug, frames, single, payload, LabelledTree.Ordered, LabelledTree.inorder]

example : ∃ u : LabelledTree Nat, ∃ rotations cost,
    u.erase = pair.tree ∧ u.inorder = original.inorder ∧ u.Ordered ∧
    LabelledTree.Rotations original u rotations ∧ rotations ≤ cost ∧
    Pointer.Trace ⟨original.erase, []⟩ ⟨pair.tree, []⟩ cost ∧ cost + pair.potential ≤ 72 := by
  have labelled := Results.extract_build_labelled
    (show Positive unitWeight original from HeavyPath.Results.unit_positive original)
    (by decide) originalOrdered
  simpa only [extracted, pair, frames, List.length_cons, List.length_nil] using labelled

-- Four upper separators trigger a Chocolate carry/freeze. Its reflected
-- pointer trace has the same six repair instructions plus three per frame.
private def carryFrames : List (Frame Nat) := [.left 1 .nil, .left 2 .nil, .left 3 .nil, .left 4 .nil]

example : Stacks.buildCost unitWeight carryFrames Stacks.empty = 18 := by
  norm_num [Stacks.buildCost, Stacks.pushCost, Stacks.push, Stacks.empty, carryFrames,
    Layer.push, Layer.pushCost, unitWeight, mass, WeightedTree.mass, Layer.decode,
    Regulars.attach, Icing.decode]

example : (Stacks.build unitWeight carryFrames Stacks.empty).upper.Valid 0 := by
  exact (Results.build_valid carryFrames Results.empty_valid (by
    norm_num [carryFrames, frameMass, mass, unitWeight])).2

example : Pointer.Trace ⟨Stacks.empty.tree, carryFrames.map Frame.erase⟩
    ⟨(Stacks.build unitWeight carryFrames Stacks.empty).tree, []⟩
    (Stacks.buildCost unitWeight carryFrames Stacks.empty) := by
  simpa only [List.append_nil] using Results.build_trace unitWeight carryFrames Stacks.empty []

example : Stacks.build unitWeight [] Stacks.empty = Stacks.empty := rfl
example : Stacks.buildCost unitWeight [] Stacks.empty = 0 := rfl

end RotationBST.Tests.PairedHeavyPath
