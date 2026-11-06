module

public import RotationBST.Algorithms.Deamortization.Scheduler.Height
public import RotationBST.Algorithms.Deamortization.Window.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Deamortization.Scheduler

theorem response_exists {budget : Nat} {s : State} {request : Request}
    (valid : Valid budget s) (ready : ∃ finish, Prepared budget s.planned request finish) :
    ∃ out, Correct budget s request out := by
  obtain ⟨finish, executed, visit, height⟩ := ready
  let ops := s.pending ++ request.instructions
  have replay : Multifinger.replay ops s.cursor = some finish := by
    simpa only [ops, Multifinger.replay_append, valid.2.1, Option.bind_some] using executed
  have allHeight : Height budget s.cursor ops := height_append valid.2.1 valid.2.2 height
  obtain ⟨cut, visited, length, first, key⟩ := visit
  have visits : ∃ cut visited, cut ≤ ops.length ∧
      Multifinger.replay (ops.take cut) s.cursor = some visited ∧ visited.key? = some request.target := by
    refine ⟨s.pending.length + cut, visited, ?_, ?_, key⟩
    · simp only [ops, List.length_append]
      omega
    · simpa only [ops, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, Multifinger.replay_append, valid.2.1, Option.bind_some] using first
  have target : request.target < s.cursor.tree.size := by
    have existsKey := visited.key_lt_size _ key
    obtain ⟨_, _, firstRotations⟩ := (Multifinger.Replay.Results.physical first).rotations
    obtain ⟨_, _, pendingRotations⟩ := (Multifinger.Replay.Results.physical valid.2.1).rotations
    rw [← firstRotations.size_eq, ← pendingRotations.size_eq] at existsKey
    exact existsKey
  obtain ⟨consumed, middle, touched, before, after, within, length, prefixReplay, suffixReplay,
    outward, touchedKey, backward, work, worst, _⟩ := Window.Results.serve replay valid.1 target visits allHeight
  let next : State := ⟨middle, ops.drop consumed, finish⟩
  have nextValid : Valid budget next := ⟨Pointer.Detour.Results.trace_nonempty
    (Multifinger.Replay.Results.physical prefixReplay) valid.1, suffixReplay, height_drop prefixReplay allHeight⟩
  exact ⟨⟨next, touched, before, after, consumed⟩, nextValid, executed, within, length, rfl,
    prefixReplay, outward, touchedKey, backward, by simpa [Response.instructions] using work,
    by
      change 1 + (before ++ after).length ≤ 1 + 5 * budget
      simp only [List.length_append]
      omega⟩

/-- One choice per current state and current request; no future requests enter. -/
noncomputable def policy (budget : Nat) : Policy := by
  classical
  exact fun s request =>
    if valid : Valid budget s then
      if ready : ∃ finish, Prepared budget s.planned request finish then
        some (Classical.choose (response_exists valid ready))
      else none
    else none

theorem policy_valid (budget : Nat) : PolicyValid budget (policy budget) := by
  classical
  intro s request valid ready
  exact ⟨Classical.choose (response_exists valid ready), by simp [policy, valid, ready],
    Classical.choose_spec (response_exists valid ready)⟩

theorem policy_exists (budget : Nat) : ∃ p : Policy, PolicyValid budget p :=
  ⟨policy budget, policy_valid budget⟩

end RotationBST.Deamortization.Scheduler
