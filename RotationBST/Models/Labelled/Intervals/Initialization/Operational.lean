module

public import RotationBST.Models.Labelled.Intervals.Initialization.Traversal
public import RotationBST.Models.Pointer.Walk.Basic
public import RotationBST.Models.Pointer.Keys
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.IntervalMetadata.Initialization
open Pointer

theorem tick_walk {s t : State} {cost : Nat} (transition : tick s = some (cost, t)) :
    ∃ moves, moves ≤ cost ∧ Pointer.Walk s.cursor t.cursor moves := by
  rcases s with ⟨⟨focus, cs⟩, fields, pending, mode⟩
  unfold tick at transition
  split at transition <;> simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
  all_goals obtain ⟨rfl, rfl⟩ := transition
  · exact ⟨0, by decide, .refl⟩
  · exact ⟨0, by decide, .refl⟩
  · exact ⟨1, by decide, .step .downLeft .refl⟩
  · exact ⟨0, by decide, .refl⟩
  · exact ⟨1, by decide, .step .downRight .refl⟩
  · exact ⟨1, by decide, .step .upLeft .refl⟩
  · exact ⟨1, by decide, .step .upRight .refl⟩

theorem Run.walk {s t : State} {cost : Nat} (run : Run s t cost) :
    ∃ moves, moves ≤ cost ∧ Pointer.Walk s.cursor t.cursor moves := by
  induction run with
  | refl => exact ⟨0, Nat.le_refl _, .refl⟩
  | step first _ ih =>
    obtain ⟨a, ha, walk⟩ := tick_walk first
    obtain ⟨b, hb, tail⟩ := ih
    exact ⟨a + b, by omega, walk.append tail⟩

theorem Run.tree {s t : State} {cost : Nat} (run : Run s t cost) : s.cursor.tree = t.cursor.tree := by
  obtain ⟨_, _, walk⟩ := run.walk
  exact walk.tree_eq

/-- The write phase changes the two bound words at exactly the cursor node. -/
theorem write_local (l r : Tree) (cs : List Frame) (fields : Nat → Bounds) (pending : Bounds) :
    Metadata.Write (Metadata.label fields (plug cs (.node l r)) 0) (offset cs + l.size) pending
      (Metadata.label (Function.update fields (offset cs + l.size) pending) (plug cs (.node l r)) 0) := by
  apply Metadata.label_write
  · exact Nat.zero_le _
  · simpa only [Nat.zero_add, Config.tree] using (Config.key_lt_size ⟨.node l r, cs⟩ _ rfl)

theorem tick_bounded {limit : Nat} {s t : State} {cost : Nat} (transition : tick s = some (cost, t))
    (bounded : s.Bounded limit) : t.Bounded limit := by
  have same : t.cursor.tree = s.cursor.tree := by
    obtain ⟨_, _, walk⟩ := tick_walk transition
    exact walk.tree_eq.symm
  refine ⟨by rw [same]; exact bounded.1, ?_⟩
  rcases s with ⟨⟨focus, cs⟩, fields, pending, mode⟩
  have keyBound : ∀ l r, focus = .node l r → offset cs + l.size < limit := by
    intro l r tree
    have key := Config.key_lt_size (Config.mk focus cs) (offset cs + l.size) (by rw [tree]; rfl)
    exact lt_of_lt_of_le key bounded.1
  cases mode <;> cases focus with
  | nil => simp only [tick, reduceCtorEq] at transition
  | node l r =>
    first
    | -- The write phase.
      change some (2, _) = some (cost, t) at transition
      obtain ⟨rfl, rfl⟩ := Option.some.inj transition
      refine ⟨bounded.2.1, bounded.2.2.1, ?_⟩
      intro x
      by_cases sameKey : x = offset cs + l.size
      · subst x; simpa only [Function.update_self] using And.intro bounded.2.1 bounded.2.2.1
      · simpa only [Function.update_of_ne sameKey] using bounded.2.2.2 x
    | -- Try the left-child dispatch.
      cases l with
      | nil =>
        change some (1, _) = some (cost, t) at transition
        obtain ⟨rfl, rfl⟩ := Option.some.inj transition
        exact bounded.2
      | node a b =>
        change some (4, _) = some (cost, t) at transition
        obtain ⟨rfl, rfl⟩ := Option.some.inj transition
        exact ⟨(bounded.2.2.2 _).1, (keyBound _ _ rfl).le, bounded.2.2.2⟩
    | -- Try the right-child dispatch.
      cases r with
      | nil =>
        change some (1, _) = some (cost, t) at transition
        obtain ⟨rfl, rfl⟩ := Option.some.inj transition
        exact bounded.2
      | node a b =>
        change some (4, _) = some (cost, t) at transition
        obtain ⟨rfl, rfl⟩ := Option.some.inj transition
        exact ⟨keyBound _ _ rfl, (bounded.2.2.2 _).2, bounded.2.2.2⟩
    | -- A return changes no fields or bound registers.
      cases cs with
      | nil => simp only [tick, reduceCtorEq] at transition
      | cons frame cs =>
        cases frame <;> change some (1, _) = some (cost, t) at transition <;>
          obtain ⟨rfl, rfl⟩ := Option.some.inj transition <;> exact bounded.2

theorem Run.bounded {limit : Nat} {s t : State} {cost : Nat} (run : Run s t cost)
    (bounded : s.Bounded limit) : t.Bounded limit := by
  induction run with
  | refl => exact bounded
  | step first _ ih => exact ih (tick_bounded first bounded)

end RotationBST.IntervalMetadata.Initialization
