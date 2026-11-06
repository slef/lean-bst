module

public import RotationBST.Structures.TreeBuffer.Snapshot.Controller.Normalization
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Controller
open Multifinger

/-- Pause the local controller after a specified number of emitted opcodes.
Silent control transitions remain legal and do not consume packet capacity. -/
theorem Run.split {s t : State} {ops : List Opcode} (run : Run s ops t) (count : Nat)
    (fits : count ≤ ops.length) :
    ∃ middle, Run s (ops.take count) middle ∧ Run middle (ops.drop count) t := by
  induction run generalizing count with
  | refl =>
    have zero : count = 0 := Nat.eq_zero_of_le_zero fits
    subst count
    exact ⟨_, .refl, .refl⟩
  | silent first _ ih =>
    obtain ⟨middle, left, right⟩ := ih count fits
    exact ⟨middle, .silent first left, right⟩
  | instruction first rest ih =>
    cases count with
    | zero => exact ⟨_, .refl, .instruction first rest⟩
    | succ count =>
      obtain ⟨middle, left, right⟩ := ih count (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using fits)
      exact ⟨middle, .instruction first left, right⟩

/-- Produce the next packet: four emitted opcodes, or the entire remaining
stream when the controller halts sooner. No full log is required at runtime. -/
theorem Run.packet {s t : State} {ops : List Opcode} (run : Run s ops t) (halt : tick t = none) :
    ∃ middle, Run s (ops.take 4) middle ∧ Run middle (ops.drop 4) t ∧
      ((ops.take 4).length = 4 ∨ tick middle = none) := by
  by_cases full : 4 ≤ ops.length
  · obtain ⟨middle, left, right⟩ := run.split 4 full
    exact ⟨middle, left, right, Or.inl (by simp only [List.length_take, Nat.min_eq_left full])⟩
  · have fits : ops.length ≤ 4 := by omega
    refine ⟨t, ?_, ?_, Or.inr halt⟩
    · simpa only [List.take_of_length_le fits] using run
    · simpa only [List.drop_eq_nil_of_le fits] using (Run.refl (s := t))

end RotationBST.TreeBuffer.Snapshot.Controller
