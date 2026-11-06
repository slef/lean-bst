module

public import RotationBST.Models.Labelled.Intervals.Access.Definitions.Abstract
public import RotationBST.Models.Labelled.Cursor.Operational
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.IntervalMetadata.Access
open LabelledCursor

theorem focus_label (cs : List (Frame (Nat × Bounds))) (focus : LabelledTree (Nat × Bounds))
    (lo : Nat) (canonical : plug cs focus = label (plug cs focus).erase lo) :
    focus = label focus.erase (lo + Pointer.offset (cs.map Frame.erase)) := by
  induction cs generalizing focus with
  | nil => simpa only [plug, List.map_nil, Pointer.offset, Nat.add_zero] using canonical
  | cons frame cs ih =>
    cases frame with
    | left entry r =>
      have parent := ih (.node focus entry r) canonical
      simp only [LabelledTree.erase, label, LabelledTree.node.injEq] at parent
      simpa only [List.map_cons, Frame.erase, Pointer.offset] using parent.1
    | right l entry =>
      have parent := ih (.node l entry focus) canonical
      simp only [LabelledTree.erase, label, LabelledTree.node.injEq] at parent
      simpa only [List.map_cons, Frame.erase, Pointer.offset, Nat.add_assoc] using parent.2.2

/-- Correctness of the words actually read, without recomputing the key from
subtree sizes in the executable routing code. -/
theorem read_valid (c : Config (Nat × Bounds)) (canonical : Canonical c)
    (key : Nat) (bounds : Bounds) (read : c.read = some (key, bounds)) :
    (Pointer.Routing.View.mk bounds.low key bounds.high).Valid c.erase := by
  rcases c with ⟨focus, cs⟩
  have fields := focus_label cs focus 0 canonical
  cases focus with
  | nil => simp [Config.read] at read
  | node l entry r =>
    cases Option.some.inj read
    simp only [LabelledTree.erase, label, LabelledTree.node.injEq, Prod.mk.injEq,
      Nat.zero_add] at fields
    obtain ⟨_, ⟨keyEq, boundsEq⟩, _⟩ := fields
    subst key
    subst bounds
    exact ⟨rfl, rfl, rfl⟩

end RotationBST.IntervalMetadata.Access
