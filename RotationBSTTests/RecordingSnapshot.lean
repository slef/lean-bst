module

public import RotationBST.Structures.TreeBuffer.Snapshot.Recording.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.RecordingSnapshot
open Multifinger TreeBuffer Snapshot Recording

private def leaf : Tree := .node .nil .nil
private def saved : Tree := .node leaf .nil
private def normalized : Tree := .node .nil leaf
private def data : Nat → Nat := fun _ => 99
private def control : Controller.State := ⟨⟨normalized, []⟩, 0, .ascend⟩
private def afterRotation : Scan.State := ⟨normalized, 1, 0, false⟩
private def firstScan : Scan.State := ⟨normalized, 0, 1, false⟩
private def lastScan : Scan.State := ⟨normalized, 1, 2, false⟩
private def firstData : Nat → Nat := Function.update data 0 1506
private def lastData : Nat → Nat := Function.update firstData 1 0
private def final : State := ⟨control, lastScan, lastData⟩

-- A full packet includes the normalization rotation and its subsequent
-- descent/return; the remaining cell is padded with zero.
example : record saved = [.downLeft, .rotateLeftChild, .downRight, .upRight] := by decide
example : encodedCells saved = [1506, 0] := by decide
private theorem firstWrite : Cells.Trace ⟨afterRotation, data⟩ ⟨firstScan, firstData⟩ [.write 0 1506] 2 0 :=
  .step (.navigate (a := ⟨leaf, [.right .nil]⟩) (b := ⟨normalized, []⟩)
    rfl .upRight rfl rfl (by decide) (by decide))
    (.step (.write 1506 (by decide) (by decide) rfl) .refl)
private theorem lastWrite : Cells.Trace ⟨firstScan, firstData⟩ ⟨lastScan, lastData⟩ [.write 1 0] 2 0 :=
  .step (.navigate (a := ⟨normalized, []⟩) (b := ⟨leaf, [.right .nil]⟩)
    rfl .downRight rfl rfl (by decide) (by decide))
    (.step (.write 0 (by decide) (by decide) rfl) .refl)
private theorem padding : Run ⟨control, firstScan, firstData⟩ final [] 2 0 :=
  .packet (s := ⟨control, firstScan, firstData⟩) .refl (by decide) (Or.inr rfl) .refl (by decide) lastWrite (.done .refl rfl (by decide))
private theorem recording : Run (initial saved data) final (record saved) 4 1 := by
  simpa only [List.append_nil] using Run.packet (s := initial saved data) (Controller.normalization saved)
    (by decide) (Or.inr rfl) (.step (.rotate .right) .refl) (by decide) firstWrite padding

example : lastData 0 = 1506 ∧ lastData 1 = 0 ∧ lastData 2 = 99 := by decide
example : CellIO.Stored saved lastData := Results.stored saved data recording (by decide)
example : Scan.Trace (initial saved data).scan lastScan 4 1 := Results.buffer recording
example : Controller.Run (initial saved data).control (record saved) control := Results.controller recording
example : 4 + (record saved).length ≤ 4 * saved.size + 4 * (record saved).length :=
  Results.cost recording (initial_valid saved data (by decide))

-- A full four-opcode packet may pause before the controller halts.
private def three : Tree := .node saved .nil
example : ∃ middle,
    Controller.Run ⟨⟨three, []⟩, 0, .scan⟩ ((record three).take 4) middle ∧
    Controller.Run middle ((record three).drop 4) ⟨⟨vine three.size, []⟩, 0, .ascend⟩ ∧
    (((record three).take 4).length = 4 ∨ Controller.tick middle = none) :=
  (Controller.normalization three).packet rfl
example : encodeCell ((record three).take 4) = 1800 := by decide

-- A right vine halts after a two-opcode partial packet, followed by padding.
example : record normalized = [.downRight, .upRight] := by decide
example : encodedCells normalized = [30, 0] := by decide

example : ∃ finalData cost, Save data saved finalData cost ∧ CellIO.Stored saved finalData ∧
    cost ≤ 72 * saved.size := Results.save saved data
example : ∃ finalData cost, Save data leaf finalData cost ∧ CellIO.Stored leaf finalData ∧
    cost ≤ 72 := Results.save leaf data
example : ∃ finalData cost, Save data .nil finalData cost ∧ CellIO.Stored .nil finalData ∧
    cost ≤ 0 := Results.save .nil data

end RotationBST.Tests.RecordingSnapshot
