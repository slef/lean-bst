module

public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Operational
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Streaming
open Multifinger

theorem rotations_scan {a b : Tree} {r : Nat} (rotations : Rotations a b r)
    (s : Scan.State) (tree : s.tree = a) :
    Scan.Trace s { s with tree := b } 0 r := by
  induction rotations generalizing s with
  | refl => simpa only [← tree] using (Scan.Trace.refl (s := s))
  | @step a b c r first rest ih =>
    have step : Scan.Step s { s with tree := b } 0 1 := .rotate (by simpa only [tree] using first)
    simpa only [Nat.zero_add, Nat.add_comm 1] using Scan.Trace.step step (ih { s with tree := b } rfl)

/-- Successful remaining replay makes every pending instruction legal. With
no retained packet, the machine advances the buffer by one charged action. -/
theorem next_exists (data : Nat → Nat) (s : State) (valid : s.Valid)
    (target : Pointer.Config) (executable : replay (remaining data s) s.cursor = some target)
    (unfinished : ¬ s.Done) : ∃ t w p r, Step data s t w p r := by
  cases packet : s.packet with
  | nil =>
    have pending : s.scan.requests ≠ [] := fun empty => unfinished ⟨packet, empty⟩
    obtain ⟨t, first⟩ := Scan.next_exists s.scan valid.2.1 pending
    cases first with
    | move tree move key next pending closer =>
      exact ⟨_, 1, 0, 0, .navigate packet (.navigate tree move key next pending closer)⟩
    | visit pending arrived =>
      exact ⟨_, 1, 0, 0, .read packet (.read valid.2.1.1 pending arrived)⟩
  | cons op ops =>
    cases first : perform op s.cursor with
    | none => simp only [remaining, packet, List.cons_append, replay, first, Option.bind_none, reduceCtorEq] at executable
    | some cursor =>
      obtain ⟨r, bound, rotations⟩ := (perform_sound first).rotations
      exact ⟨_, 0, 1, r, .execute packet first (rotations_scan rotations s.scan valid.1.symm) bound⟩

theorem Step.executable {data : Nat → Nat} {s t : State} {w p r : Nat}
    (step : Step data s t w p r) (target : Pointer.Config)
    (executable : replay (remaining data s) s.cursor = some target) :
    replay (remaining data t) t.cursor = some target := by
  obtain ⟨ops, _, stream, run⟩ := step.stream
  simpa only [stream, replay_append, run, Option.bind_some] using executable

theorem Trace.valid {data : Nat → Nat} {s t : State} {w p r : Nat}
    (trace : Trace data s t w p r) (valid : s.Valid) : t.Valid := by
  induction trace with
  | refl => exact valid
  | step first _ ih => exact ih (first.valid valid)

theorem Trace.scan {data : Nat → Nat} {s t : State} {w p r : Nat}
    (trace : Trace data s t w p r) : Scan.Trace s.scan t.scan w r := by
  induction trace with
  | refl => exact .refl
  | step first _ ih => exact first.scan.append ih

theorem Trace.stream {data : Nat → Nat} {s t : State} {w p r : Nat}
    (trace : Trace data s t w p r) :
    ∃ ops, ops.length = p ∧ remaining data s = ops ++ remaining data t ∧
      replay ops s.cursor = some t.cursor := by
  induction trace with
  | refl => exact ⟨[], rfl, rfl, rfl⟩
  | step first _ ih =>
    obtain ⟨ops, length, stream, run⟩ := first.stream
    obtain ⟨tail, tailLength, tailStream, tailRun⟩ := ih
    exact ⟨ops ++ tail, by simp only [List.length_append, length, tailLength],
      by rw [stream, tailStream, List.append_assoc],
      by rw [replay_append, run, Option.bind_some, tailRun]⟩

theorem Trace.amortized {data : Nat → Nat} {s t : State} {w p r : Nat}
    (trace : Trace data s t w p r) (valid : s.Valid) :
    w + p + potential data t ≤ potential data s := by
  induction trace with
  | refl => simp
  | step first _ ih =>
    have bound := first.potential_bound valid
    have rest := ih (first.valid valid)
    omega

/-- Projection onto the replay finger uses exactly the charged opcode count. -/
theorem Trace.physical {data : Nat → Nat} {s t : State} {w p r : Nat}
    (trace : Trace data s t w p r) : Pointer.Trace s.cursor t.cursor p := by
  obtain ⟨ops, length, _, run⟩ := trace.stream
  simpa only [length] using replay_trace run

/-- The input list is only used to establish legality in the proof. The
machine itself retains at most one packet and reads the next node on demand. -/
theorem finish (data : Nat → Nat) (s : State) (valid : s.Valid)
    (target : Pointer.Config) (executable : replay (remaining data s) s.cursor = some target) :
    ∃ t w p r, Trace data s t w p r ∧ t.Done ∧ w + p ≤ potential data s := by
  generalize amount : potential data s = fuel
  induction fuel using Nat.strong_induction_on generalizing s with
  | ind fuel ih =>
    by_cases done : s.Done
    · exact ⟨s, 0, 0, 0, .refl, done, Nat.zero_le _⟩
    · obtain ⟨t, w, p, r, first⟩ := next_exists data s valid target executable done
      have bound := first.potential_bound valid
      have positive := first.positive
      have smaller : potential data t < fuel := by omega
      obtain ⟨u, v, q, h, rest, done, cost⟩ := ih (potential data t) smaller t (first.valid valid)
        (first.executable target executable) rfl
      exact ⟨u, w + v, p + q, r + h, .step first rest, done, by omega⟩

theorem completed {data : Nat → Nat} {s t : State} {w p r : Nat}
    (trace : Trace data s t w p r) (done : t.Done) :
    replay (remaining data s) s.cursor = some t.cursor ∧ p = (remaining data s).length := by
  obtain ⟨ops, length, stream, run⟩ := trace.stream
  have empty : remaining data t = [] := by simp [remaining, done.1, done.2, CellIO.inverseCells]
  rw [empty, List.append_nil] at stream
  exact ⟨by simpa only [stream] using run, by rw [stream, length]⟩

end RotationBST.TreeBuffer.Snapshot.Streaming
