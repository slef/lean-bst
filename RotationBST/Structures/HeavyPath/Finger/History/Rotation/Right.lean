module

public import RotationBST.Structures.HeavyPath.Finger.History.Rotation.Left
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Rotation
open Paired Recursive LabelledCursor PopTart PopTart.Chocolate Recursive.History

/-- Promote a right source child with the same complete-state cost bound. -/
theorem rotateRightChild_within {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.right sibling parent :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs (.node sibling parent l) key r next ∧
      Pointer.TraceWithin (fun t => t.size = s.pair.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth s.pair.tree x + 56) ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 50 + s.potential ∧ next.ancestors = s.ancestors.tail ∧
      (cost : ℝ) ≤ 22 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨e, es, ancestors, source, context⟩ := Up.split_context valid.context
  have member : e ∈ s.ancestors := by rw [ancestors]; exact List.mem_cons_self
  have siblingLayout : Layout weight sibling e.shape e.credit := by
    simpa only [source, framePayload] using valid.children e member
  have parentPositive : 0 < weight parent := by
    simpa only [source, frameKey] using (frame_positive valid member).2
  obtain ⟨shape, credit, joinCost, joined, joinTrace, joinBound, joinWorst⟩ :=
    layout_join_within siblingLayout valid.leftLayout parentPositive
  have shapeNonempty : shape ≠ .nil := by
    have size := layout_size joined
    intro empty
    rw [empty] at size
    simp only [Tree.size, LabelledTree.erase] at size
    omega
  have nextPositive : Positive weight (plug cs (.node (.node sibling parent l) key r)) := by
    apply (positive_context_congr weight cs (.node sibling parent (.node l key r))
      (.node (.node sibling parent l) key r) (by simp only [Positive, and_assoc])).mp
    exact valid.positive
  obtain ⟨before, carry, carryNonnegative, ending⟩ := Down.sideSlots_end
    (fun f hf => (frame_positive valid (by
      rw [ancestors]
      exact List.mem_cons_of_mem _ (lower_mem hf))).2)
    (show (0 : ℝ) ≤ 0 from le_rfl)
  let slots := sideSlots weight sibling e.shape 0 (Recursive.History.lower es)
  have oldLower : s.pair.lower.decode.mirror.fringe = slots ++ [(s.leftShape, mass weight l + weight parent)] := by
    rw [valid.lower, ancestors]
    simp only [Recursive.History.lower, source, Down.sideSlots_append]
    change slots ++ [(s.leftShape, weight parent + mass weight l)] = _
    rw [add_comm (weight parent)]
  have suffixNonempty : (slots.map reflectSlot).reverse ≠ [] := by
    intro empty
    have eq := List.map_eq_nil_iff.mp (List.reverse_eq_nil_iff.mp empty)
    exact Up.sideSlots_nonempty weight sibling e.shape 0 (Recursive.History.lower es) eq
  obtain ⟨rest, popped, restValid, restFringe, _, popBound⟩ :=
    Chocolate.Top.Results.pop_front valid.pair.1 (Up.raw_of_back oldLower) suffixNonempty
  have restBack : rest.decode.mirror.fringe = before ++ [(e.shape, carry + mass weight sibling)] := by
    rw [Up.mirror_of_raw restFringe]
    exact ending sibling e.shape
  have stored := Down.top_back restValid restBack
  let newCharge := carry + mass weight (.node sibling parent l)
  let nextPair : Pair := ⟨rest.replaceTop (.leaf shape.mirror newCharge), s.pair.upper⟩
  let next : State α := ⟨es, shape, s.rightShape, credit, s.rightCredit, nextPair⟩
  obtain ⟨cost, trace, traceBound⟩ := Transfer.Interruption.rotateRight_within popped stored newCharge shapeNonempty joinTrace
  have chargeNonnegative : 0 ≤ newCharge := add_nonneg carryNonnegative
    (mass_nonnegative (positive_nonnegative (layout_positive joined)))
  have unchanged := Chocolate.Top.Results.replaceTop_potential restValid (.leaf shape.mirror newCharge)
  refine ⟨next, cost, ?_, trace, ?_, ?_, ?_⟩
  · refine ⟨nextPositive, context, ⟨Chocolate.Top.Results.replaceTop_valid restValid
        (.leaf _ _) chargeNonnegative, valid.pair.2⟩, joined, valid.rightLayout, ?_, ?_, ?_⟩
    · intro f hf
      exact valid.children f (by rw [ancestors]; exact List.mem_cons_of_mem _ hf)
    · change (rest.replaceTop (.leaf shape.mirror newCharge)).decode.mirror.fringe =
        sideSlots weight (.node sibling parent l) shape 0 (Recursive.History.lower es)
      rw [ending]
      exact Up.replace_back stored restBack
    · simpa only [ancestors, Recursive.History.upper, source] using valid.upper
  · change cost + (nextPair.potential + credit + s.rightCredit + (es.map Entry.credit).sum) ≤ 50 + s.potential
    have oldPotential : s.potential = s.pair.potential + s.leftCredit + s.rightCredit +
        (e.credit + (es.map Entry.credit).sum) := by
      simp only [State.potential, ancestors, List.map_cons, List.sum_cons]
    have newPotential : nextPair.potential = rest.potential + s.pair.upper.potential := by
      change (rest.replaceTop _).potential + s.pair.upper.potential = _
      rw [unchanged]
    rw [oldPotential, newPotential, Pair.potential]
    omega
  · rw [ancestors]
    rfl
  · have size : (Tree.node e.shape s.leftShape).size ≤ s.pair.tree.size := by
      rw [state_size valid]
      have enclosing := focus_size_le cs (.node sibling parent (.node l key r))
      simp only [LabelledCursor.plug, LabelledTree.erase, Tree.size,
        layout_size siblingLayout, layout_size valid.leftLayout] at enclosing ⊢
      omega
    have logarithm : Real.logb 2 (Tree.node e.shape s.leftShape).size ≤ Real.logb 2 s.pair.tree.size := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · simp only [Tree.size, Nat.cast_add, Nat.cast_one]
        positivity
      · exact_mod_cast size
    have stackWorst := Population.Results.lower_pop valid.pair
    have work : (cost : ℝ) ≤ s.pair.lower.popCost + joinCost + 6 := by
      exact_mod_cast traceBound
    linarith

theorem rotateRightChild_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.right sibling parent :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs (.node sibling parent l) key r next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 50 + s.potential ∧ next.ancestors = s.ancestors.tail ∧
      (cost : ℝ) ≤ 22 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨next, cost, nextValid, trace, amortized, ancestors, worst⟩ := rotateRightChild_within valid
  exact ⟨next, cost, nextValid, trace.trace, amortized, ancestors, worst⟩

theorem rotateRightChild {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.right sibling parent :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs (.node sibling parent l) key r next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 50 + s.potential ∧ next.ancestors = s.ancestors.tail := by
  obtain ⟨next, cost, nextValid, trace, amortized, ancestors, _⟩ := rotateRightChild_bounded valid
  exact ⟨next, cost, nextValid, trace, amortized, ancestors⟩

end RotationBST.HeavyPath.Finger.History.Rotation
