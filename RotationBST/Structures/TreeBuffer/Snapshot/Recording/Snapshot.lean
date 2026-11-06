module

public import RotationBST.Structures.TreeBuffer.Snapshot.Recording.Layout
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Load
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Recording
open Multifinger

theorem initial_requests (tree : Tree) (data : Nat → Nat) :
    (initial tree data).scan.requests = List.range tree.size := by
  simp [initial, Scan.State.requests, ← List.range_eq_range']

theorem initial_valid (tree : Tree) (data : Nat → Nat) (nonempty : tree ≠ .nil) :
    (initial tree data).Valid :=
  ⟨rfl, Streaming.rootPosition_valid tree nonempty, Nat.zero_le _⟩

private theorem zip_writes (keys : List Nat) (target : Nat → Nat) :
    List.zipWith Cells.Event.write keys (keys.map target) = keys.map (fun x => Cells.Event.write x (target x)) := by
  induction keys with
  | nil => rfl
  | cons x xs ih => simpa only [List.map_cons, List.zipWith_cons_cons] using congrArg (Cells.Event.write x (target x) :: ·) ih

/-- Completing a recording of the normalizer stores exactly its canonical
encoded snapshot, with actual charged writes in forward key order. -/
theorem Run.stored (tree : Tree) (data : Nat → Nat) {t : State} {work rotations : Nat}
    (run : Run (initial tree data) t (record tree) work rotations) (nonempty : tree ≠ .nil) :
    CellIO.Stored tree t.data := by
  have cells := run.cells (initial_valid tree data nonempty)
  rw [initial_requests, List.length_range] at cells
  change Cells.Trace ⟨(initial tree data).scan, data⟩ ⟨t.scan, t.data⟩
    (List.zipWith Cells.Event.write (List.range tree.size) (encodedCells tree)) work rotations at cells
  have values := CellIO.stored_values tree (CellIO.payload tree) (fun _ _ => rfl)
  rw [← values, zip_writes] at cells
  intro x present
  simpa only [List.mem_range, present, ↓reduceIte] using cells.writes x

/-- Produce and write the snapshot while normalizing, retaining at most one
four-opcode packet. All pointer instructions and node writes are charged. -/
theorem record_snapshot (tree : Tree) (data : Nat → Nat) :
    ∃ t work rotations, Run (initial tree data) t (record tree) work rotations ∧
      t.control = ⟨⟨vine tree.size, []⟩, 0, .ascend⟩ ∧ CellIO.Stored tree t.data ∧
      work + (record tree).length ≤ 20 * tree.size := by
  by_cases empty : tree = .nil
  · subst tree
    refine ⟨⟨⟨⟨.nil, []⟩, 0, .ascend⟩, (initial .nil data).scan, data⟩, 0, 0,
      .done (Controller.normalization .nil) rfl rfl, rfl, ?_, Nat.le_refl _⟩
    intro x present
    exact False.elim (Nat.not_lt_zero _ present)
  · have valid := initial_valid tree data empty
    obtain ⟨t, work, rotations, run, control⟩ := produce (initial tree data) valid
      ⟨⟨vine tree.size, []⟩, 0, .ascend⟩ (record tree) (Controller.normalization tree) rfl
      (by simpa only [initial_requests, List.length_range] using record_length tree)
    have cost := run.cost valid
    have length := record_length tree
    exact ⟨t, work, rotations, run, control, run.stored tree data empty, by dsimp only [initial] at cost; omega⟩

/-- A complete shape-preserving save, including online packet production,
charged node writes, and streaming restoration. It leaves the snapshot in the
same nodes and uses at most 72n pointer/I/O units in the current scan model. -/
theorem save (tree : Tree) (data : Nat → Nat) :
    ∃ finalData cost, Save data tree finalData cost ∧ CellIO.Stored tree finalData ∧ cost ≤ 72 * tree.size := by
  by_cases empty : tree = .nil
  · subst tree
    refine ⟨data, 0, ?_, ?_, Nat.le_refl _⟩
    · exact ⟨⟨⟨⟨.nil, []⟩, 0, .ascend⟩, (initial .nil data).scan, data⟩, [], 0, 0,
        Streaming.initial .nil 0, 0, 0, 0,
        .done (Controller.normalization .nil) rfl rfl, rfl, .refl, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
    · intro x present; exact False.elim (Nat.not_lt_zero _ present)
  · obtain ⟨t, work, rotations, run, control, stored, cost⟩ := record_snapshot tree data
    have valid := run.valid (initial_valid tree data empty)
    have shape : t.scan.tree = vine tree.size := by
      have alignment := valid.1
      rw [control] at alignment
      exact alignment.symm
    have position : t.scan.position < tree.size := by
      have present := valid.2.1
      simpa only [shape, vine_size] using present
    obtain ⟨u, reads, instructions, replayRotations, restore, done, result, _, restoreCost⟩ :=
      Streaming.restore_from tree t.data stored t.scan.position position
    refine ⟨t.data, (record tree).length + work + reads + instructions, ?_, stored, by omega⟩
    refine ⟨t, record tree, work, rotations, u, reads, instructions, replayRotations,
      run, ?_, ?_, done, result, rfl, rfl⟩
    · rw [control, shape]
    · simpa only [shape] using restore

end RotationBST.TreeBuffer.Snapshot.Recording
