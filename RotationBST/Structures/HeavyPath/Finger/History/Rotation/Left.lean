module

public import RotationBST.Structures.HeavyPath.Finger.History.Up.Slots
public import RotationBST.Structures.HeavyPath.Finger.Transfer.Rotation.Local
public import RotationBST.Structures.HeavyPath.Finger.Transfer.Interruption.Rotation
public import RotationBST.Structures.HeavyPath.Recursive.History.Join
public import RotationBST.Structures.HeavyPath.Finger.History.Population
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Rotation
open Paired Recursive LabelledCursor PopTart PopTart.Chocolate Recursive.History

theorem positive_context_congr {α : Type} (weight : α → ℝ) (cs : List (Frame α))
    (a b : LabelledTree α) (same : Positive weight a ↔ Positive weight b) :
    Positive weight (plug cs a) ↔ Positive weight (plug cs b) := by
  induction cs generalizing a b with
  | nil => exact same
  | cons f cs ih =>
    cases f <;> apply ih <;> simp only [Positive, same]

/-- Promote a left source child. The two payloads separated by its parent
are joined, while the represented finger remains at the physical root. -/
theorem rotateLeftChild_within {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.left parent sibling :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs l key (.node r parent sibling) next ∧
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
    layout_join_within valid.rightLayout siblingLayout parentPositive
  have shapeNonempty : shape ≠ .nil := by
    have size := layout_size joined
    intro empty
    rw [empty] at size
    simp only [Tree.size, LabelledTree.erase] at size
    omega
  have nextPositive : Positive weight (plug cs (.node l key (.node r parent sibling))) := by
    apply (positive_context_congr weight cs (.node (.node l key r) parent sibling)
      (.node l key (.node r parent sibling)) (by simp only [Positive, and_assoc])).mp
    exact valid.positive
  obtain ⟨before, carry, carryNonnegative, ending⟩ := Down.sideSlots_end
    (fun f hf => (frame_positive valid (by
      rw [ancestors]
      exact List.mem_cons_of_mem _ (upper_mem (List.mem_reverse.mp hf)))).2)
    (show (0 : ℝ) ≤ 0 from le_rfl)
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
    exact Up.sideSlots_nonempty weight sibling e.shape 0 (Recursive.History.upper es).reverse eq
  obtain ⟨rest, popped, restValid, restFringe, _, popBound⟩ :=
    Chocolate.Top.Results.pop_front valid.pair.2 oldUpper suffixNonempty
  have restFront : rest.decode.fringe = (e.shape, carry + mass weight sibling) :: before.reverse := by
    rw [restFringe]
    change (sideSlots weight sibling e.shape 0 (Recursive.History.upper es).reverse).reverse = _
    rw [ending, List.reverse_append, List.reverse_singleton, List.singleton_append]
  have stored := Down.top_front restValid restFront
  let newCharge := carry + mass weight (.node r parent sibling)
  let nextPair : Pair := ⟨s.pair.lower, rest.replaceTop (.leaf shape newCharge)⟩
  let next : State α := ⟨es, s.leftShape, shape, s.leftCredit, credit, nextPair⟩
  obtain ⟨cost, trace, traceBound⟩ := Transfer.Interruption.rotateLeft_within popped stored newCharge shapeNonempty joinTrace
  have chargeNonnegative : 0 ≤ newCharge := add_nonneg carryNonnegative
    (mass_nonnegative (positive_nonnegative (layout_positive joined)))
  have unchanged := Chocolate.Top.Results.replaceTop_potential restValid (.leaf shape newCharge)
  refine ⟨next, cost, ?_, trace, ?_, ?_, ?_⟩
  · refine ⟨nextPositive, context, ⟨valid.pair.1, Chocolate.Top.Results.replaceTop_valid restValid
        (.leaf _ _) chargeNonnegative⟩, valid.leftLayout, joined, ?_, ?_, ?_⟩
    · intro f hf
      exact valid.children f (by rw [ancestors]; exact List.mem_cons_of_mem _ hf)
    · simpa only [ancestors, Recursive.History.lower, source] using valid.lower
    · change (rest.replaceTop (.leaf shape newCharge)).decode.fringe =
        (sideSlots weight (.node r parent sibling) shape 0 (Recursive.History.upper es).reverse).reverse
      rw [ending, List.reverse_append, List.reverse_singleton, List.singleton_append]
      exact Up.replace_front stored restFront
  · change cost + (nextPair.potential + s.leftCredit + credit + (es.map Entry.credit).sum) ≤ 50 + s.potential
    have oldPotential : s.potential = s.pair.potential + s.leftCredit + s.rightCredit +
        (e.credit + (es.map Entry.credit).sum) := by
      simp only [State.potential, ancestors, List.map_cons, List.sum_cons]
    have newPotential : nextPair.potential = s.pair.lower.potential + rest.potential := by
      change s.pair.lower.potential + (rest.replaceTop _).potential = _
      rw [unchanged]
    rw [oldPotential, newPotential, Pair.potential]
    omega
  · rw [ancestors]
    rfl
  · have size : (Tree.node s.rightShape e.shape).size ≤ s.pair.tree.size := by
      rw [state_size valid]
      have enclosing := focus_size_le cs (.node (.node l key r) parent sibling)
      simp only [LabelledCursor.plug, LabelledTree.erase, Tree.size,
        layout_size valid.rightLayout, layout_size siblingLayout] at enclosing ⊢
      omega
    have logarithm : Real.logb 2 (Tree.node s.rightShape e.shape).size ≤ Real.logb 2 s.pair.tree.size := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · simp only [Tree.size, Nat.cast_add, Nat.cast_one]
        positivity
      · exact_mod_cast size
    have stackWorst := Population.Results.upper_pop valid.pair
    have work : (cost : ℝ) ≤ s.pair.upper.popCost + joinCost + 6 := by
      exact_mod_cast traceBound
    linarith

theorem rotateLeftChild_bounded {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.left parent sibling :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs l key (.node r parent sibling) next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 50 + s.potential ∧ next.ancestors = s.ancestors.tail ∧
      (cost : ℝ) ≤ 22 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨next, cost, nextValid, trace, amortized, ancestors, worst⟩ := rotateLeftChild_within valid
  exact ⟨next, cost, nextValid, trace.trace, amortized, ancestors, worst⟩

theorem rotateLeftChild {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {l r sibling : LabelledTree α} {key parent : α} {s : State α}
    (valid : Valid weight (.left parent sibling :: cs) l key r s) :
    ∃ (next : State α) (cost : Nat), Valid weight cs l key (.node r parent sibling) next ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨next.pair.tree, []⟩ cost ∧
      cost + next.potential ≤ 50 + s.potential ∧ next.ancestors = s.ancestors.tail := by
  obtain ⟨next, cost, nextValid, trace, amortized, ancestors, _⟩ := rotateLeftChild_bounded valid
  exact ⟨next, cost, nextValid, trace, amortized, ancestors⟩

end RotationBST.HeavyPath.Finger.History.Rotation
