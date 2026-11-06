module

public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Refinement.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Shared.Execution
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Operational
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Streaming.Refinement

theorem reads_nil (data : Nat → Nat) : Reads data [] := by intro event member; cases member

theorem reads_one (data : Nat → Nat) (key : Nat) : Reads data [.read key (data key)] := by
  intro event member
  exact ⟨key, List.mem_singleton.mp member⟩

theorem reads_append {data : Nat → Nat} {first last : List (Cells.Event Nat)}
    (one : Reads data first) (two : Reads data last) : Reads data (first ++ last) := by
  intro event member
  rcases List.mem_append.mp member with left | right
  · exact one event left
  · exact two event right

/-- One streaming step has a shared-node realization. Buffer navigation pays
four units; each replay instruction pays at most fifteen, including metadata. -/
theorem step {data : Nat → Nat} {s t : State} {w p r : Nat} (operation : Step data s t w p r)
    (valid : s.Valid) (actual : Shared.State Nat 2) (represented : Represents actual s data) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ Represents final t data ∧
      Reads data events ∧ cost ≤ 4 * w + 15 * p := by
  cases operation with
  | navigate empty cell =>
    obtain ⟨a, b, y, tree, move, key, next, pending, closer, scanEq⟩ := Cells.navigate_inv cell
    cases scanEq
    have same : s.scan.tree = actual.tree.erase := valid.1.symm.trans represented.2.1.symm
    obtain ⟨final, action, shape, positions⟩ := Shared.navigate_matching actual data represented.1 1 a b s.scan.target y
      (tree.trans same) (by simpa only [represented.2.2.2] using key) move next
      (by rw [← same]; exact Scan.target_valid s.scan valid.2.1 pending)
      (by simpa only [← same, represented.2.2.2] using closer)
    refine ⟨final, [], 4, action.trace, ?_, reads_nil data, by decide⟩
    refine ⟨action.valid data represented.1, ?_, ?_, ?_⟩
    · exact shape.trans (move.tree_eq.symm.trans (tree.trans valid.1.symm))
    · simpa only [positions, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)] using represented.2.2.1
    · simp only [positions, Function.update_self]
  | read empty cell =>
    have scanEq := Cells.read_scan cell
    cases scanEq
    have action := Shared.read_exists actual data represented.1 1
    refine ⟨actual, [.read (actual.position 1) (data (actual.position 1))], 1, action.trace,
      ?_, reads_one data _, by decide⟩
    exact ⟨represented.1, represented.2.1, represented.2.2.1, represented.2.2.2⟩
  | execute packet execution scan bound =>
    rename_i op ops cursor
    obtain ⟨nextKey, atNext⟩ := (Multifinger.perform_sound execution).keys_exist.2
    obtain ⟨final, cost, action, charged, shape, positions⟩ := Shared.execute_exists actual data represented.1 0
      op s.cursor cursor represented.2.1.symm represented.2.2.1 execution nextKey atNext
    refine ⟨final, [], cost, action.trace, ?_, reads_nil data, ?_⟩
    · refine ⟨action.valid data represented.1, shape, ?_, ?_⟩
      · simpa only [positions, Function.update_self] using atNext
      · simpa only [positions, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)] using represented.2.2.2
    · simpa only [Nat.mul_zero, Nat.mul_one, Nat.zero_add] using charged

end RotationBST.TreeBuffer.Snapshot.Streaming.Refinement
