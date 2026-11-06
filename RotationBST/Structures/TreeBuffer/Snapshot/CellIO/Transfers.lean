module

public import RotationBST.Structures.TreeBuffer.Snapshot.CellIO.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Encoding
public import RotationBST.Structures.TreeBuffer.Cells.Complete
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.CellIO

theorem payload_bound (saved : Tree) (key : Nat) : payload saved key < 2 ^ 12 := by
  unfold payload
  cases entry : (encodedCells saved)[key]? with
  | none => simp
  | some code =>
    exact encodedCells_bound saved code (List.mem_of_getElem? entry)

theorem stored_values (saved : Tree) (data : Nat → Nat) (stored : Stored saved data) :
    (List.range saved.size).map data = encodedCells saved := by
  apply List.ext_getElem
  · simp [encodedCells_length]
  · intro i left right
    have valid : i < saved.size := by simpa using left
    simp only [List.getElem_map, List.getElem_range]
    rw [stored i valid]
    simp [payload, List.getElem?_eq_getElem right]

/-- Write the encoded snapshot into a tree of the same size using charged
cursor-local writes. This theorem takes the encoded values as an input stream;
it does not yet couple their generation to the normalizer's execution. -/
theorem store (saved current : Tree) (same : current.size = saved.size)
    (position : Nat) (present : position < current.size) (data : Nat → Nat) :
    ∃ t final work, Cells.Trace ⟨⟨current, position, 0, false⟩, data⟩ ⟨t, final⟩
      ((List.range saved.size).map fun x => Cells.Event.write x (payload saved x)) work 0 ∧
      t.requests = [] ∧ work ≤ 4 * current.size ∧ Stored saved final ∧
      (∀ x, saved.size ≤ x → final x = data x) := by
  obtain ⟨t, final, work, run, done, bound, effect⟩ :=
    Cells.write_all current position present (payload saved) data
  refine ⟨t, final, work, by simpa only [same] using run, done, bound, ?_, ?_⟩
  · intro x valid
    rw [effect]
    simp [same, valid]
  · intro x outside
    rw [effect]
    simp [same, Nat.not_lt.mpr outside]

/-- Reading every node recovers the encoded snapshot exactly, with all reads
and navigation charged. The representation is independent of current shape. -/
theorem read (saved current : Tree) (same : current.size = saved.size)
    (position : Nat) (present : position < current.size) (data : Nat → Nat)
    (stored : Stored saved data) :
    ∃ t events work, Cells.Trace ⟨⟨current, position, 0, false⟩, data⟩ ⟨t, data⟩ events work 0 ∧
      t.requests = [] ∧ work ≤ 4 * current.size ∧
      events.map Cells.Event.value = encodedCells saved ∧
      decodeCells (events.map Cells.Event.value) = record saved := by
  obtain ⟨t, work, run, done, bound⟩ := Cells.read_all current position present data
  have values : ((List.range current.size).map fun x => Cells.Event.read x (data x)).map Cells.Event.value =
      encodedCells saved := by
    simpa only [List.map_map, Function.comp_def, Cells.Event.value, same] using stored_values saved data stored
  exact ⟨t, _, work, run, done, bound, values, by rw [values, decodeCells_encoded]⟩

/-- The same exact decoding applies to a completed scan interrupted by any
legal rotations. The bound explicitly charges their effect on navigation. -/
theorem read_interleaved (saved : Tree) (data : Nat → Nat) (stored : Stored saved data)
    {s t : Scan.State} {work rotations : Nat} (trace : Scan.Trace s t work rotations)
    (valid : s.Valid) (pending : s.requests = List.range saved.size) (done : t.requests = []) :
    ∃ events, Cells.Trace ⟨s, data⟩ ⟨t, data⟩ events work rotations ∧
      events.map Cells.Event.value = encodedCells saved ∧
      decodeCells (events.map Cells.Event.value) = record saved ∧
      work ≤ 4 * s.tree.size + 3 * rotations := by
  have run := Cells.read_complete trace valid done data
  have values : (s.requests.map fun x => Cells.Event.read x (data x)).map Cells.Event.value =
      encodedCells saved := by
    simpa only [List.map_map, Function.comp_def, Cells.Event.value, pending] using stored_values saved data stored
  exact ⟨_, run, values, by rw [values, decodeCells_encoded], trace.cost valid⟩

end RotationBST.TreeBuffer.Snapshot.CellIO
