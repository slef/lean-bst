module

public import RotationBST.Models.Labelled.Intervals.Maintenance.Local
public import RotationBST.Models.Labelled.Cursor.Operational
public import RotationBST.Models.Pointer.Traces
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.IntervalMetadata.Maintenance
open LabelledCursor

theorem maintain_update (side : Side) {s t : State} (execution : maintain side s = some t) :
    Update s.cursor.tree t.cursor.tree := by
  rcases s with ⟨⟨focus, cs⟩, oldChild, oldParent⟩
  cases focus with
  | nil => cases side <;> simp [maintain, program, run, tick, Config.read] at execution
  | node a entry b =>
    cases cs with
    | nil => cases side <;> simp [maintain, program, run, tick, Config.read, perform] at execution
    | cons frame cs =>
      rcases entry with ⟨x, bx⟩
      cases frame with
      | left entry c =>
        rcases entry with ⟨y, byBounds⟩
        cases side with
        | right => simp [maintain, program, run, tick, Config.read, perform] at execution
        | left =>
          rw [maintain_left] at execution
          cases Option.some.inj execution
          exact update_plug (.right a b c x y bx byBounds) cs
      | right c entry =>
        rcases entry with ⟨y, byBounds⟩
        cases side with
        | left => simp [maintain, program, run, tick, Config.read, perform] at execution
        | right =>
          rw [maintain_right] at execution
          cases Option.some.inj execution
          exact update_plug (.left c a b y x byBounds bx) cs

/-- A successful maintenance call restores the complete canonical annotation,
including every untouched ancestor and subtree. -/
theorem maintain_canonical (side : Side) {s t : State} (execution : maintain side s = some t)
    (canonical : s.cursor.tree = label s.cursor.tree.erase 0) :
    t.cursor.tree = label t.cursor.tree.erase 0 :=
  update_canonical (maintain_update side execution) 0 canonical

theorem tick_physical (op : Op) {s t : State} (execution : tick op s = some t) :
    Pointer.Trace s.cursor.erase t.cursor.erase op.moves := by
  cases op with
  | pointer opcode =>
    obtain ⟨cursor, physical, rfl⟩ : ∃ cursor, perform opcode s.cursor = some cursor ∧
        { s with cursor := cursor } = t := by simpa [tick, Option.bind_eq_some_iff] using execution
    exact .step (perform_physical physical) .refl
  | readChild =>
    obtain ⟨entry, _, rfl⟩ : ∃ entry, s.cursor.read = some entry ∧ { s with child := entry } = t := by
      simpa [tick, Option.bind_eq_some_iff] using execution
    exact .refl
  | readParent =>
    obtain ⟨entry, _, rfl⟩ : ∃ entry, s.cursor.read = some entry ∧ { s with parent := entry } = t := by
      simpa [tick, Option.bind_eq_some_iff] using execution
    exact .refl
  | writeChild side | writeParent side =>
    rcases s with ⟨⟨focus, cs⟩, child, parent⟩
    cases focus <;> simp [tick, writeBounds] at execution
    subst t
    exact .refl

/-- Every completed instruction list has an actual pointer trace. Word
operations leave the pointer fixed, rather than hiding uncharged navigation. -/
theorem run_physical (ops : List Op) {s t : State} (execution : run ops s = some t) :
    Pointer.Trace s.cursor.erase t.cursor.erase (pointerCount ops) := by
  induction ops generalizing s with
  | nil => cases Option.some.inj execution; exact .refl
  | cons op ops ih =>
    obtain ⟨next, first, rest⟩ : ∃ next, tick op s = some next ∧ run ops next = some t := by
      simpa only [run, Option.bind_eq_some_iff] using execution
    have trace := (tick_physical op first).append (ih rest)
    cases op <;> simpa [pointerCount, Op.moves, List.filter_cons, Nat.add_comm] using trace

theorem maintain_physical (side : Side) {s t : State} (execution : maintain side s = some t) :
    Pointer.Trace s.cursor.erase t.cursor.erase 5 := by
  simpa only [program_pointers] using run_physical (program side) execution

/-- Every legal child promotion has a charged, cursor-local implementation
that returns with all interval fields correct. -/
theorem implement (side : Side) (s : State) (target : Pointer.Config)
    (legal : Multifinger.perform side.opcode s.cursor.erase = some target)
    (canonical : s.cursor.tree = label s.cursor.tree.erase 0) :
    ∃ t, maintain side s = some t ∧ t.cursor.erase = target ∧
      t.cursor.tree = label t.cursor.tree.erase 0 ∧
      charge (program side) = 15 ∧ Pointer.Trace s.cursor.erase t.cursor.erase 5 := by
  have mapped := maintain_refines side s
  rw [legal] at mapped
  obtain ⟨t, execution, erased⟩ := Option.map_eq_some_iff.mp mapped
  exact ⟨t, execution, erased, maintain_canonical side execution canonical,
    program_charge side, maintain_physical side execution⟩

end RotationBST.IntervalMetadata.Maintenance
