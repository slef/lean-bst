module

public import RotationBST.Tango.State.ComponentPath.Abstract
public import RotationBST.Tango.State.Nesting.ExecutableReplacement

@[expose] public section
namespace RotationBST.Tango.MarkedTree

private theorem componentAt_nil (path : List Nat) (child : MarkedTree)
    (found : MarkedTree.nil.componentAt path = some child) : child = .nil := by
  induction path with
  | nil => exact (Option.some.inj found).symm
  | cons i rest ih =>
    cases i with
    | zero => exact ih found
    | succ i => simp [componentAt, fringe] at found

/-- A fixed local algorithm executes at any component depth with the same
amortized bound. Its exact nesting effect follows the reference fringe path,
even when every actual auxiliary component has a different binary shape. -/
theorem editAt_simulates (path : List Nat) (s reference child : MarkedTree)
    (target : ComponentNesting) (bound : ℝ) (edit : MarkedTree → MarkedTree × Nat)
    (same : s.nesting = reference.nesting) (found : reference.componentAt path = some child)
    (nonempty : child ≠ .nil)
    (localUpdate : ∀ actual : MarkedTree, actual.nesting = child.nesting →
      (edit actual).1.nesting = target ∧ Rotations actual.tree (edit actual).1.tree (edit actual).2 ∧
      ((edit actual).2 : ℝ) + (edit actual).1.potential - actual.potential ≤ bound) :
    (s.editAt path edit).1.nesting = reference.nesting.replaceAt path target ∧
      Rotations s.tree (s.editAt path edit).1.tree (s.editAt path edit).2 ∧
      ((s.editAt path edit).2 : ℝ) + (s.editAt path edit).1.potential - s.potential ≤ bound := by
  induction path generalizing s reference with
  | nil =>
    have h : reference = child := Option.some.inj found
    subst reference
    exact localUpdate s same
  | cons i rest ih =>
    cases atIndex : reference.fringe[i]? with
    | none => simp [componentAt, atIndex] at found
    | some next =>
      have tail : next.componentAt rest = some child := by simpa only [componentAt, atIndex, Option.bind_some] using found
      have nextNonempty : next ≠ .nil := by
        intro empty
        subst next
        exact nonempty (componentAt_nil rest child tail)
      have nestingAt : reference.nesting.fringe[i]? = some next.nesting := by
        rw [nesting_fringe, List.getElem?_map, atIndex]
        rfl
      have lifted := editFringe_nesting s reference next (next.nesting.replaceAt rest target)
        i bound (fun actual => actual.editAt rest edit) same atIndex nextNonempty
        (fun actual nested => ih actual next nested tail)
      simpa only [editAt, ComponentNesting.replaceAt, nestingAt] using lifted

end RotationBST.Tango.MarkedTree
