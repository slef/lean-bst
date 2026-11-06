module

public import RotationBST.Algorithms.Deamortization.Scheduler.Definitions.Abstract
public import RotationBST.Models.Multifinger.Program.Replay.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Deamortization.Scheduler

theorem height_append {budget : Nat} {a b : Pointer.Config} {xs ys : List Multifinger.Opcode}
    (first : Multifinger.replay xs a = some b) (left : Height budget a xs) (right : Height budget b ys) :
    Height budget a (xs ++ ys) := by
  intro cut middle replay
  by_cases early : cut ≤ xs.length
  · apply left cut middle
    simpa only [List.take_append_of_le_length early] using replay
  · apply right (cut - xs.length) middle
    have enough : xs.length ≤ cut := by omega
    simpa only [List.take_append, List.take_of_length_le enough,
      Multifinger.replay_append, first, Option.bind_some] using replay

theorem height_drop {budget cut : Nat} {a b : Pointer.Config} {ops : List Multifinger.Opcode}
    (first : Multifinger.replay (ops.take cut) a = some b) (height : Height budget a ops) :
    Height budget b (ops.drop cut) := by
  intro later middle replay
  apply height (cut + later) middle
  simpa only [List.take_add, Multifinger.replay_append, first, Option.bind_some] using replay

theorem initial_valid {budget : Nat} {cursor : Pointer.Config} (live : cursor.focus ≠ .nil)
    (depths : ∀ x < cursor.tree.size, Tree.depth cursor.tree x ≤ budget) :
    Valid budget (initial cursor) := by
  refine ⟨live, rfl, ?_⟩
  intro cut middle replay
  simp only [initial, List.take_nil, Multifinger.replay, Option.some.injEq] at replay
  subst middle
  exact depths

end RotationBST.Deamortization.Scheduler
