module

public import RotationBST.Structures.HeavyPath.Finger.History.Down.Slots
public import RotationBST.Structures.HeavyPath.Finger.History.Down.Fringe
public import RotationBST.Structures.HeavyPath.Finger.Transfer.History.Abstract
public import RotationBST.Structures.HeavyPath.Finger.Transfer.History.Proofs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Down
open Paired Recursive LabelledCursor Recursive.History

/-- Enter the left source child, retaining every untouched payload occurrence
and charging the new outer stack and all recursive credits together. -/
theorem downLeft_within {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key x : α} {s : State α}
    (valid : Valid weight cs (.node l x r) key sibling s) :
    ∃ (next : State α) (cost : Nat), Valid weight (.left key sibling :: cs) l x r next ∧
      Pointer.TraceWithin (fun t => t.size = s.pair.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth s.pair.tree x + 64) ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 54 + s.potential ∧
      next.ancestors = ⟨.left key sibling, s.rightShape, s.rightCredit⟩ :: s.ancestors ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨before, carry, carryNonnegative, ending⟩ := sideSlots_end
    (fun e he => (frame_positive valid (lower_mem he)).2) (show (0 : ℝ) ≤ 0 from le_rfl)
  have oldLower := valid.lower.trans (ending (.node l x r) s.leftShape)
  have stored := top_back valid.pair.1 oldLower
  have keyPositive := ((context_positive cs _ valid.positive).1).2.1
  obtain ⟨a, b, leftCredit, rightCredit, cost, leftLayout, rightLayout, trace, pairValid, bound, _, _, worst⟩ :=
    Transfer.History.downLeft_within valid.pair valid.leftLayout carryNonnegative keyPositive.le stored
  let nextPair := s.pair.downLeft a b (carry + mass weight l) (weight key + mass weight r)
  let entry : Entry α := ⟨.left key sibling, s.rightShape, s.rightCredit⟩
  let next : State α := ⟨entry :: s.ancestors, a, b, leftCredit, rightCredit, nextPair⟩
  have rightNN := mass_nonnegative (positive_nonnegative (layout_positive rightLayout))
  obtain ⟨found, oldFringe, newLower, newUpper⟩ :=
    downLeft_fringe valid.pair stored (carry + mass weight l) (add_nonneg keyPositive.le rightNN)
  have same : found = before := List.append_cancel_right (oldFringe.symm.trans oldLower)
  subst found
  refine ⟨next, cost, ?_, trace, ?_, rfl, worst⟩
  · refine ⟨valid.positive, ?_, pairValid, leftLayout, rightLayout, ?_, ?_, ?_⟩
    · change entry.source :: s.ancestors.map Entry.source = _
      rw [valid.context]
    · intro e he
      rcases List.mem_cons.mp he with rfl | earlier
      · exact valid.rightLayout
      · exact valid.children e earlier
    · change nextPair.lower.decode.mirror.fringe = sideSlots weight l a 0 (Recursive.History.lower s.ancestors)
      rw [ending]
      exact newLower
    · change nextPair.upper.decode.fringe =
        (sideSlots weight r b 0 ((entry :: Recursive.History.upper s.ancestors).reverse)).reverse
      rw [List.reverse_cons, sideSlots_append]
      change nextPair.upper.decode.fringe =
        (sideSlots weight sibling s.rightShape 0 (Recursive.History.upper s.ancestors).reverse ++
          [(b, weight key + mass weight r)]).reverse
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append, ← valid.upper]
      exact newUpper
  · change cost + (nextPair.potential + leftCredit + rightCredit +
      (s.rightCredit + (s.ancestors.map Entry.credit).sum)) ≤
      54 + (s.pair.potential + s.leftCredit + s.rightCredit + (s.ancestors.map Entry.credit).sum)
    change cost + nextPair.potential + leftCredit + rightCredit ≤ 54 + s.pair.potential + s.leftCredit at bound
    omega

theorem downLeft_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key x : α} {s : State α}
    (valid : Valid weight cs (.node l x r) key sibling s) :
    ∃ (next : State α) (cost : Nat), Valid weight (.left key sibling :: cs) l x r next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 54 + s.potential ∧
      next.ancestors = ⟨.left key sibling, s.rightShape, s.rightCredit⟩ :: s.ancestors ∧
      (cost : ℝ) ≤ 26 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨next, cost, nextValid, trace, amortized, ancestors, worst⟩ := downLeft_within valid
  exact ⟨next, cost, nextValid, trace.trace, amortized, ancestors, worst⟩

theorem downLeft {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key x : α} {s : State α}
    (valid : Valid weight cs (.node l x r) key sibling s) :
    ∃ (next : State α) (cost : Nat), Valid weight (.left key sibling :: cs) l x r next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 54 + s.potential ∧
      next.ancestors = ⟨.left key sibling, s.rightShape, s.rightCredit⟩ :: s.ancestors := by
  obtain ⟨next, cost, nextValid, trace, amortized, ancestors, _⟩ := downLeft_bounded valid
  exact ⟨next, cost, nextValid, trace, amortized, ancestors⟩

end RotationBST.HeavyPath.Finger.History.Down
