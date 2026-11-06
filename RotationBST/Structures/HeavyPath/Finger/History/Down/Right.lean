module

public import RotationBST.Structures.HeavyPath.Finger.History.Down.Left
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Down
open Paired Recursive LabelledCursor Recursive.History

/-- Enter the right source child with the same whole-state potential bound. -/
theorem downRight_within {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key x : α} {s : State α}
    (valid : Valid weight cs sibling key (.node l x r) s) :
    ∃ (next : State α) (cost : Nat), Valid weight (.right sibling key :: cs) l x r next ∧
      Pointer.TraceWithin (fun t => t.size = s.pair.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth s.pair.tree x + 64) ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 54 + s.potential ∧
      next.ancestors = ⟨.right sibling key, s.leftShape, s.leftCredit⟩ :: s.ancestors ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨before, carry, carryNonnegative, ending⟩ := sideSlots_end
    (fun e he => (frame_positive valid (upper_mem (List.mem_reverse.mp he))).2)
    (show (0 : ℝ) ≤ 0 from le_rfl)
  have oldUpper : s.pair.upper.decode.fringe =
      (s.rightShape, carry + mass weight (.node l x r)) :: before.reverse := by
    rw [valid.upper, ending, List.reverse_append, List.reverse_singleton, List.singleton_append]
  have stored := top_front valid.pair.2 oldUpper
  have keyPositive := ((context_positive cs _ valid.positive).1).2.1
  obtain ⟨a, b, leftCredit, rightCredit, cost, leftLayout, rightLayout, trace, pairValid, bound, _, _, worst⟩ :=
    Transfer.History.downRight_within valid.pair valid.rightLayout carryNonnegative keyPositive.le stored
  let nextPair := s.pair.downRight a b (weight key + mass weight l) (carry + mass weight r)
  let entry : Entry α := ⟨.right sibling key, s.leftShape, s.leftCredit⟩
  let next : State α := ⟨entry :: s.ancestors, a, b, leftCredit, rightCredit, nextPair⟩
  have leftNN := mass_nonnegative (positive_nonnegative (layout_positive leftLayout))
  obtain ⟨found, oldFringe, newUpper, newLower⟩ :=
    downRight_fringe valid.pair stored (carry + mass weight r) (add_nonneg keyPositive.le leftNN)
  have same : found = before.reverse := (List.cons.inj (oldFringe.symm.trans oldUpper)).2
  rw [same] at newUpper
  refine ⟨next, cost, ?_, trace, ?_, rfl, worst⟩
  · refine ⟨valid.positive, ?_, pairValid, leftLayout, rightLayout, ?_, ?_, ?_⟩
    · change entry.source :: s.ancestors.map Entry.source = _
      rw [valid.context]
    · intro e he
      rcases List.mem_cons.mp he with rfl | earlier
      · exact valid.leftLayout
      · exact valid.children e earlier
    · change nextPair.lower.decode.mirror.fringe =
        sideSlots weight l a 0 (Recursive.History.lower s.ancestors ++ [entry])
      rw [sideSlots_append]
      change nextPair.lower.decode.mirror.fringe =
        sideSlots weight sibling s.leftShape 0 (Recursive.History.lower s.ancestors) ++
          [(a, weight key + mass weight l)]
      rw [← valid.lower]
      exact newLower
    · change nextPair.upper.decode.fringe =
        (sideSlots weight r b 0 (Recursive.History.upper s.ancestors).reverse).reverse
      rw [ending, List.reverse_append, List.reverse_singleton, List.singleton_append]
      exact newUpper
  · change cost + (nextPair.potential + leftCredit + rightCredit +
      (s.leftCredit + (s.ancestors.map Entry.credit).sum)) ≤
      54 + (s.pair.potential + s.leftCredit + s.rightCredit + (s.ancestors.map Entry.credit).sum)
    change cost + nextPair.potential + leftCredit + rightCredit ≤ 54 + s.pair.potential + s.rightCredit at bound
    omega

theorem downRight_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key x : α} {s : State α}
    (valid : Valid weight cs sibling key (.node l x r) s) :
    ∃ (next : State α) (cost : Nat), Valid weight (.right sibling key :: cs) l x r next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 54 + s.potential ∧
      next.ancestors = ⟨.right sibling key, s.leftShape, s.leftCredit⟩ :: s.ancestors ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨next, cost, nextValid, trace, amortized, ancestors, worst⟩ := downRight_within valid
  exact ⟨next, cost, nextValid, trace.trace, amortized, ancestors, worst⟩

theorem downRight {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key x : α} {s : State α}
    (valid : Valid weight cs sibling key (.node l x r) s) :
    ∃ (next : State α) (cost : Nat), Valid weight (.right sibling key :: cs) l x r next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 54 + s.potential ∧
      next.ancestors = ⟨.right sibling key, s.leftShape, s.leftCredit⟩ :: s.ancestors := by
  obtain ⟨next, cost, nextValid, trace, amortized, ancestors, _⟩ := downRight_bounded valid
  exact ⟨next, cost, nextValid, trace, amortized, ancestors⟩

end RotationBST.HeavyPath.Finger.History.Down
