module

public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.CellIO.Reverse
public import RotationBST.Models.Pointer.Keys
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Streaming
open Multifinger

theorem decodeFuel_length (fuel code : Nat) : (decodeFuel fuel code).length ≤ fuel := by
  induction fuel generalizing code with
  | zero => rfl
  | succ fuel ih =>
    simp only [decodeFuel]
    split
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (ih _)

theorem packet_bound (code : Nat) : (undo (decodeCell code)).length ≤ 12 := by
  have decoded := decodeFuel_length 4 code
  have inverse := undo_length (decodeCell code)
  change (decodeCell code).length ≤ 4 at decoded
  omega

theorem Step.scan {data : Nat → Nat} {s t : State} {w p r : Nat} (step : Step data s t w p r) :
    Scan.Trace s.scan t.scan w r := by
  cases step with
  | navigate _ cell => exact .step cell.scan .refl
  | read _ cell => exact .step cell.scan .refl
  | execute _ _ scan _ => exact scan

private theorem scan_fixed {s t : Scan.State} {w : Nat} (step : Scan.Step s t w 0) :
    s.tree = t.tree := by
  cases step with
  | move tree move _ _ _ _ => exact tree.symm.trans move.tree_eq
  | visit _ _ => rfl

private theorem updated_requests (s : Scan.State) (tree : Tree) (same : s.tree.size = tree.size) :
    s.requests = ({ s with tree := tree } : Scan.State).requests := by
  simp only [Scan.State.requests, same]

theorem Step.valid {data : Nat → Nat} {s t : State} {w p r : Nat} (step : Step data s t w p r)
    (valid : s.Valid) : t.Valid := by
  refine ⟨?_, step.scan.valid valid.2.1, ?_⟩
  · cases step with
    | navigate _ cell => exact valid.1.trans (scan_fixed cell.scan)
    | read _ cell => exact valid.1.trans (scan_fixed cell.scan)
    | execute _ _ _ _ => rfl
  · cases step with
    | navigate _ _ => exact Nat.zero_le _
    | read _ _ => exact packet_bound _
    | execute packet _ _ _ => have bound := valid.2.2; rw [packet, List.length_cons] at bound; dsimp; omega

theorem Step.rotations_le {data : Nat → Nat} {s t : State} {w p r : Nat}
    (step : Step data s t w p r) : r ≤ p := by
  cases step with
  | navigate _ _ => exact Nat.le_refl _
  | read _ _ => exact Nat.le_refl _
  | execute _ _ _ bound => exact bound

theorem Step.positive {data : Nat → Nat} {s t : State} {w p r : Nat}
    (step : Step data s t w p r) : w + p = 1 := by cases step <;> rfl

theorem Step.stream {data : Nat → Nat} {s t : State} {w p r : Nat}
    (step : Step data s t w p r) :
    ∃ ops, ops.length = p ∧ remaining data s = ops ++ remaining data t ∧
      replay ops s.cursor = some t.cursor := by
  cases step with
  | navigate empty cell =>
    refine ⟨[], rfl, ?_, rfl⟩
    have requests := cell.requests
    simp only [Option.toList_none, List.map_nil, List.nil_append] at requests
    simp only [remaining, empty, List.nil_append, requests]
  | read empty cell =>
    refine ⟨[], rfl, ?_, rfl⟩
    have requests := cell.requests
    have value := (Cells.read_at cell).2.1
    simp only [Option.toList_some, List.map_cons, List.map_nil, Cells.Event.key, List.singleton_append] at requests
    simp only [remaining, empty, List.nil_append, requests, List.map_cons,
      CellIO.inverseCells, List.flatMap_cons, value]
  | execute packet run scan bound =>
    rename_i op ops cursor
    have requests := updated_requests s.scan _ scan.size_eq
    refine ⟨[op], rfl, ?_, ?_⟩
    · simp only [remaining, packet, List.cons_append, List.nil_append, requests]
    · simp only [replay, run, Option.bind_some]

theorem Step.potential_bound {data : Nat → Nat} {s t : State} {w p r : Nat}
    (step : Step data s t w p r) (valid : s.Valid) :
    w + p + potential data t ≤ potential data s := by
  obtain ⟨ops, length, stream, _⟩ := step.stream
  have amount : (remaining data s).length = p + (remaining data t).length := by
    rw [stream, List.length_append, length]
  have scan := step.scan.amortized valid.2.1
  have rotations := step.rotations_le
  simp only [potential]
  omega

end RotationBST.TreeBuffer.Snapshot.Streaming
