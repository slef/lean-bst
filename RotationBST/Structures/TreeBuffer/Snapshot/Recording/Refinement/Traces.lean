module

public import RotationBST.Structures.TreeBuffer.Snapshot.Recording.Refinement.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Shared.Replay
public import RotationBST.Structures.TreeBuffer.Shared.CellRefinement.Traces
public import RotationBST.Structures.TreeBuffer.Snapshot.Recording.Basic
public import RotationBST.Structures.TreeBuffer.Snapshot.Encoding

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Recording.Refinement

/-- Packet production and its cell writes run on one shared labelled tree.
Each phase retains the other finger's node identity, and the complete physical
trace realizes the final cell map with all metadata work charged. -/
theorem trace_bounded {s t : State} {ops : List Multifinger.Opcode} {work rotations : Nat}
    (run : Run s t ops work rotations) (valid : s.Valid) (actual : Shared.State Nat 2)
    (represented : Represents actual s) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ Represents final t ∧
      cost ≤ 15 * ops.length + 4 * work ∧
      (∀ key value, Cells.Event.write key value ∈ events → value < 2 ^ 12) := by
  induction run generalizing actual with
  | @done s control normal halt empty =>
    have same : s.control.cursor = control.cursor := Option.some.inj normal.replay
    refine ⟨actual, [], 0, .refl, ?_, Nat.le_refl _, by simp⟩
    refine ⟨represented.1, represented.2.1.trans (congrArg Pointer.Config.tree same), ?_, represented.2.2.2⟩
    simpa only [same] using represented.2.2.1
  | @packet s u control chunk tail rotations work later more scan data key normal capacity ready rotationTrace rotationBound writes rest ih =>
    obtain ⟨middle, normalCost, normalized, shape, normalKey, normalInactive, normalBound⟩ :=
      Shared.replay chunk s.data actual represented.1 0 s.control.cursor control.cursor
        represented.2.1 represented.2.2.1 normal.replay
    have midValid : middle.Valid s.data := normalized.valid s.data represented.1
    have midBuffer : middle.position 1 = s.scan.position :=
      (normalInactive 1 (by decide)).trans represented.2.2.2
    have scanValid := rotationTrace.valid valid.2
    have cellRep : Shared.CellRefinement.Represents middle
        ⟨{ s.scan with tree := control.cursor.tree }, s.data⟩ 1 := ⟨midValid, shape, midBuffer⟩
    obtain ⟨written, writeCost, writtenTrace, writtenRep, writeInactive, writeBound⟩ :=
      Shared.CellRefinement.trace writes rfl scanValid middle 1 cellRep
    have fixed := Cells.scan_fixed writes.scan rfl
    have nextValid : (State.mk control scan data).Valid := ⟨fixed, writes.scan.valid scanValid⟩
    have nextRep : Represents written ⟨control, scan, data⟩ := by
      refine ⟨writtenRep.1, writtenRep.2.1.trans fixed.symm, ?_, writtenRep.2.2⟩
      simpa only [writeInactive 0 (by decide)] using normalKey
    obtain ⟨final, events, restCost, continuation, finalRep, restBound, restWritten⟩ := ih nextValid written nextRep
    refine ⟨final, .write key (encodeCell chunk) :: events, normalCost + (writeCost + restCost),
      normalized.append (writtenTrace.append continuation), finalRep, ?_, ?_⟩
    · simp only [List.length_append]
      omega
    · intro address value member
      rcases List.mem_cons.mp member with same | later
      · cases same
        exact encodeCell_packet_bound chunk capacity
      · exact restWritten address value later

/-- The shared trace and its logical bound, without the packet-width certificate. -/
theorem trace {s t : State} {ops : List Multifinger.Opcode} {work rotations : Nat}
    (run : Run s t ops work rotations) (valid : s.Valid) (actual : Shared.State Nat 2)
    (represented : Represents actual s) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ Represents final t ∧
      cost ≤ 15 * ops.length + 4 * work := by
  obtain ⟨final, events, cost, execution, finalRep, bound, _⟩ :=
    trace_bounded run valid actual represented
  exact ⟨final, events, cost, execution, finalRep, bound⟩

end RotationBST.TreeBuffer.Snapshot.Recording.Refinement
