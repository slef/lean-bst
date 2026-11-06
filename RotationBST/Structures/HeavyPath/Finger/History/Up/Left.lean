module

public import RotationBST.Structures.HeavyPath.Finger.History.Up.Slots
public import RotationBST.Structures.HeavyPath.Finger.Transfer.Up.Local
public import RotationBST.Structures.HeavyPath.Finger.Transfer.Interruption.Up
public import RotationBST.Structures.HeavyPath.Recursive.History.Join
public import RotationBST.Structures.HeavyPath.Finger.History.Population
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Up
open Paired Recursive LabelledCursor PopTart PopTart.Chocolate Recursive.History

/-- Return from a left child to its source parent. The departing subtree is
joined once, and every other payload occurrence retains its own history. -/
theorem upLeft_within {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.left parent sibling :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs (.node l key r) parent sibling next ∧
      Pointer.TraceWithin (fun t => t.size = s.pair.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth s.pair.tree x + 96) ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 62 + s.potential ∧ next.ancestors = s.ancestors.tail ∧
      (cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨e, es, ancestors, source, context⟩ := split_context valid.context
  have siblingLayout : Layout weight sibling e.shape e.credit := by
    have child := valid.children e (by rw [ancestors]; exact List.mem_cons_self)
    simpa only [source, framePayload] using child
  have keyPositive := ((context_positive (.left parent sibling :: cs) _ valid.positive).1).2.1
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
    (fun f hf => (frame_positive valid (by rw [ancestors]; exact List.mem_cons_of_mem _ (lower_mem hf))).2)
    (show (0 : ℝ) ≤ 0 from le_rfl)
  have oldLower : s.pair.lower.decode.mirror.fringe =
      before ++ [(s.leftShape, carry + mass weight l)] := by
    have fringe := valid.lower
    simp only [ancestors, Recursive.History.lower, source] at fringe
    exact fringe.trans (ending l s.leftShape)
  have stored := Down.top_back valid.pair.1 oldLower
  let suffix := (sideSlots weight sibling e.shape 0 (Recursive.History.upper es).reverse).reverse
  have oldUpper : s.pair.upper.decode.fringe =
      (s.rightShape, weight parent + mass weight r) :: suffix := by
    rw [valid.upper, ancestors]
    simp only [Recursive.History.upper, source, List.reverse_cons, Down.sideSlots_append]
    change (sideSlots weight sibling e.shape 0 (Recursive.History.upper es).reverse ++
      [(s.rightShape, weight parent + mass weight r)]).reverse = _
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append, suffix]
  have suffixNonempty : suffix ≠ [] := by
    intro empty
    have eq := congrArg List.reverse empty
    simp only [suffix, List.reverse_reverse, List.reverse_nil] at eq
    exact sideSlots_nonempty weight sibling e.shape 0 (Recursive.History.upper es).reverse eq
  obtain ⟨rest, popped, restValid, restFringe, _, popBound⟩ :=
    Chocolate.Top.Results.pop_front valid.pair.2 oldUpper suffixNonempty
  let newCharge := carry + mass weight (.node l key r)
  let nextPair : Pair := ⟨s.pair.lower.replaceTop (.leaf shape.mirror newCharge), rest⟩
  let next : State α := ⟨es, shape, e.shape, credit, e.credit, nextPair⟩
  obtain ⟨cost, trace, traceBound⟩ := Transfer.Interruption.upLeft_within stored popped newCharge shapeNonempty joinTrace
  have chargeNonnegative : 0 ≤ newCharge := add_nonneg carryNonnegative
    (mass_nonnegative (positive_nonnegative positive))
  have unchanged := Chocolate.Top.Results.replaceTop_potential valid.pair.1 (.leaf shape.mirror newCharge)
  refine ⟨next, cost, ?_, trace, ?_, ?_, ?_⟩
  · refine ⟨valid.positive, context, ⟨Chocolate.Top.Results.replaceTop_valid valid.pair.1
        (.leaf _ _) chargeNonnegative, restValid⟩, joined, siblingLayout, ?_, ?_, restFringe⟩
    · intro f hf
      exact valid.children f (by rw [ancestors]; exact List.mem_cons_of_mem _ hf)
    · change (s.pair.lower.replaceTop (.leaf shape.mirror newCharge)).decode.mirror.fringe =
        sideSlots weight (.node l key r) shape 0 (Recursive.History.lower es)
      rw [ending]
      exact replace_back stored oldLower
  · change cost + (nextPair.potential + credit + e.credit + (es.map Entry.credit).sum) ≤ 62 + s.potential
    have oldPotential : s.potential = s.pair.potential + s.leftCredit + s.rightCredit +
        (e.credit + (es.map Entry.credit).sum) := by
      simp only [State.potential, ancestors, List.map_cons, List.sum_cons]
    have newPotential : nextPair.potential = s.pair.lower.potential + rest.potential := by
      change (s.pair.lower.replaceTop _).potential + rest.potential = _
      rw [unchanged]
    rw [oldPotential, newPotential, Pair.potential]
    omega
  · rw [ancestors]
    rfl
  · have size : (Tree.node s.leftShape s.rightShape).size ≤ s.pair.tree.size := by
      rw [state_size valid]
      have enclosing := focus_size_le cs (.node (.node l key r) parent sibling)
      simp only [LabelledCursor.plug, LabelledTree.erase, Tree.size,
        layout_size valid.leftLayout, layout_size valid.rightLayout] at enclosing ⊢
      omega
    have logarithm : Real.logb 2 (Tree.node s.leftShape s.rightShape).size ≤ Real.logb 2 s.pair.tree.size := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · simp only [Tree.size, Nat.cast_add, Nat.cast_one]
        positivity
      · exact_mod_cast size
    have stackWorst := Population.Results.upper_pop valid.pair
    have work : (cost : ℝ) ≤ s.pair.upper.popCost + joinCost + 18 := by
      exact_mod_cast traceBound
    linarith

theorem upLeft_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.left parent sibling :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs (.node l key r) parent sibling next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 62 + s.potential ∧ next.ancestors = s.ancestors.tail ∧
      (cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨next, cost, nextValid, trace, amortized, ancestors, worst⟩ := upLeft_within valid
  exact ⟨next, cost, nextValid, trace.trace, amortized, ancestors, worst⟩

theorem upLeft {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.left parent sibling :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs (.node l key r) parent sibling next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 62 + s.potential ∧ next.ancestors = s.ancestors.tail := by
  obtain ⟨next, cost, nextValid, trace, amortized, ancestors, _⟩ := upLeft_bounded valid
  exact ⟨next, cost, nextValid, trace, amortized, ancestors⟩

end RotationBST.HeavyPath.Finger.History.Up
