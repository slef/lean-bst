module

public import RotationBST.Structures.HeavyPath.Finger.History.Up.Left
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Up
open Paired Recursive LabelledCursor PopTart PopTart.Chocolate Recursive.History

/-- Return from a right child with the same complete-state potential bound. -/
theorem upRight_within {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.right sibling parent :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs sibling parent (.node l key r) next ∧
      Pointer.TraceWithin (fun t => t.size = s.pair.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth s.pair.tree x + 96) ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 62 + s.potential ∧ next.ancestors = s.ancestors.tail ∧
      (cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨e, es, ancestors, source, context⟩ := split_context valid.context
  have siblingLayout : Layout weight sibling e.shape e.credit := by
    have child := valid.children e (by rw [ancestors]; exact List.mem_cons_self)
    simpa only [source, framePayload] using child
  have keyPositive := ((context_positive (.right sibling parent :: cs) _ valid.positive).1).2.1
  have positive : Positive weight (.node l key r) := ⟨layout_positive valid.leftLayout,
    keyPositive, layout_positive valid.rightLayout⟩
  obtain ⟨shape, credit, joinCost, joined, joinTrace, joinBound, joinWorst⟩ :=
    layout_join_within valid.leftLayout valid.rightLayout keyPositive
  have shapeNonempty : shape ≠ .nil := by
    have size := layout_size joined
    intro empty
    rw [empty] at size
    simp only [Tree.size, LabelledTree.erase] at size
    omega
  obtain ⟨before, carry, carryNonnegative, ending⟩ := Down.sideSlots_end
    (fun f hf => (frame_positive valid (by
      rw [ancestors]
      exact List.mem_cons_of_mem _ (upper_mem (List.mem_reverse.mp hf)))).2)
    (show (0 : ℝ) ≤ 0 from le_rfl)
  have oldUpper : s.pair.upper.decode.fringe =
      (s.rightShape, carry + mass weight r) :: before.reverse := by
    have fringe := valid.upper
    simp only [ancestors, Recursive.History.upper, source] at fringe
    rw [fringe, ending, List.reverse_append, List.reverse_singleton, List.singleton_append]
  have stored := Down.top_front valid.pair.2 oldUpper
  let slots := sideSlots weight sibling e.shape 0 (Recursive.History.lower es)
  have oldLower : s.pair.lower.decode.mirror.fringe = slots ++ [(s.leftShape, mass weight l + weight parent)] := by
    rw [valid.lower, ancestors]
    simp only [Recursive.History.lower, source, Down.sideSlots_append]
    change slots ++ [(s.leftShape, weight parent + mass weight l)] = _
    rw [add_comm (weight parent)]
  have suffixNonempty : (slots.map reflectSlot).reverse ≠ [] := by
    intro empty
    have eq := List.map_eq_nil_iff.mp (List.reverse_eq_nil_iff.mp empty)
    exact sideSlots_nonempty weight sibling e.shape 0 (Recursive.History.lower es) eq
  obtain ⟨rest, popped, restValid, restFringe, _, popBound⟩ :=
    Chocolate.Top.Results.pop_front valid.pair.1 (raw_of_back oldLower) suffixNonempty
  let newCharge := carry + mass weight (.node l key r)
  let nextPair : Pair := ⟨rest, s.pair.upper.replaceTop (.leaf shape newCharge)⟩
  let next : State α := ⟨es, e.shape, shape, e.credit, credit, nextPair⟩
  obtain ⟨cost, trace, traceBound⟩ := Transfer.Interruption.upRight_within stored popped newCharge shapeNonempty joinTrace
  have chargeNonnegative : 0 ≤ newCharge := add_nonneg carryNonnegative
    (mass_nonnegative (positive_nonnegative positive))
  have unchanged := Chocolate.Top.Results.replaceTop_potential valid.pair.2 (.leaf shape newCharge)
  refine ⟨next, cost, ?_, trace, ?_, ?_, ?_⟩
  · refine ⟨valid.positive, context, ⟨restValid, Chocolate.Top.Results.replaceTop_valid valid.pair.2
        (.leaf _ _) chargeNonnegative⟩, siblingLayout, joined, ?_, mirror_of_raw restFringe, ?_⟩
    · intro f hf
      exact valid.children f (by rw [ancestors]; exact List.mem_cons_of_mem _ hf)
    · change (s.pair.upper.replaceTop (.leaf shape newCharge)).decode.fringe =
        (sideSlots weight (.node l key r) shape 0 (Recursive.History.upper es).reverse).reverse
      rw [ending, List.reverse_append, List.reverse_singleton, List.singleton_append]
      exact replace_front stored oldUpper
  · change cost + (nextPair.potential + e.credit + credit + (es.map Entry.credit).sum) ≤ 62 + s.potential
    have oldPotential : s.potential = s.pair.potential + s.leftCredit + s.rightCredit +
        (e.credit + (es.map Entry.credit).sum) := by
      simp only [State.potential, ancestors, List.map_cons, List.sum_cons]
    have newPotential : nextPair.potential = rest.potential + s.pair.upper.potential := by
      change rest.potential + (s.pair.upper.replaceTop _).potential = _
      rw [unchanged]
    rw [oldPotential, newPotential, Pair.potential]
    omega
  · rw [ancestors]
    rfl
  · have size : (Tree.node s.leftShape s.rightShape).size ≤ s.pair.tree.size := by
      rw [state_size valid]
      have enclosing := focus_size_le cs (.node sibling parent (.node l key r))
      simp only [LabelledCursor.plug, LabelledTree.erase, Tree.size,
        layout_size valid.leftLayout, layout_size valid.rightLayout] at enclosing ⊢
      omega
    have logarithm : Real.logb 2 (Tree.node s.leftShape s.rightShape).size ≤ Real.logb 2 s.pair.tree.size := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · simp only [Tree.size, Nat.cast_add, Nat.cast_one]
        positivity
      · exact_mod_cast size
    have stackWorst := Population.Results.lower_pop valid.pair
    have work : (cost : ℝ) ≤ s.pair.lower.popCost + joinCost + 18 := by
      exact_mod_cast traceBound
    linarith

theorem upRight_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.right sibling parent :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs sibling parent (.node l key r) next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 62 + s.potential ∧ next.ancestors = s.ancestors.tail ∧
      (cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨next, cost, nextValid, trace, amortized, ancestors, worst⟩ := upRight_within valid
  exact ⟨next, cost, nextValid, trace.trace, amortized, ancestors, worst⟩

theorem upRight {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.right sibling parent :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs sibling parent (.node l key r) next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 62 + s.potential ∧ next.ancestors = s.ancestors.tail := by
  obtain ⟨next, cost, nextValid, trace, amortized, ancestors, _⟩ := upRight_bounded valid
  exact ⟨next, cost, nextValid, trace, amortized, ancestors⟩

end RotationBST.HeavyPath.Finger.History.Up
