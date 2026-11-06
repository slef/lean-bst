module

public import RotationBST.Models.Labelled.Intervals.Maintenance.Definitions.Abstract
public import RotationBST.Models.Labelled.Intervals.Representation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.IntervalMetadata.Maintenance
open LabelledCursor

theorem program_charge (side : Side) : charge (program side) = 15 := by cases side <;> rfl

theorem program_pointers (side : Side) : pointerCount (program side) = 5 := by cases side <;> rfl

/-- Actual execution, including both adjacent-node reads and the return from
writing the demoted parent's fields. Initial register contents are irrelevant. -/
theorem maintain_left (a b c : LabelledTree (Nat × Bounds)) (x y : Nat) (bx byBounds : Bounds)
    (cs : List (Frame (Nat × Bounds))) (oldChild oldParent : Nat × Bounds) :
    maintain .left ⟨⟨.node a (x, bx) b, .left (y, byBounds) c :: cs⟩, oldChild, oldParent⟩ =
      some ⟨⟨.node a (x, ⟨bx.low, byBounds.high⟩)
        (.node b (y, ⟨x + 1, byBounds.high⟩) c), cs⟩, (x, bx), (y, byBounds)⟩ := rfl

theorem maintain_right (a b c : LabelledTree (Nat × Bounds)) (x y : Nat) (bx byBounds : Bounds)
    (cs : List (Frame (Nat × Bounds))) (oldChild oldParent : Nat × Bounds) :
    maintain .right ⟨⟨.node b (y, byBounds) c, .right a (x, bx) :: cs⟩, oldChild, oldParent⟩ =
      some ⟨⟨.node (.node a (x, ⟨bx.low, y⟩) b)
        (y, ⟨bx.low, byBounds.high⟩) c, cs⟩, (y, byBounds), (x, bx)⟩ := rfl

/-- The maintenance routine implements precisely the requested rotation,
including failure when that child-parent edge does not exist. -/
theorem maintain_refines (side : Side) (s : State) :
    (maintain side s).map (fun t => t.cursor.erase) =
      Multifinger.perform side.opcode s.cursor.erase := by
  rcases s with ⟨⟨focus, cs⟩, child, parent⟩
  cases focus with
  | nil => cases side <;> rfl
  | node a entry b =>
    cases cs with
    | nil => cases side <;> rfl
    | cons frame cs => cases frame <;> cases side <;> rfl

theorem update_plug {s t : LabelledTree (Nat × Bounds)} (update : Update s t)
    (cs : List (Frame (Nat × Bounds))) : Update (plug cs s) (plug cs t) := by
  induction cs generalizing s t with
  | nil => exact update
  | cons frame cs ih => cases frame with
    | left entry r => exact ih (.inLeft update)
    | right l entry => exact ih (.inRight update)

theorem update_rotation {s t : LabelledTree (Nat × Bounds)} (update : Update s t) :
    Rotate s.erase t.erase := by
  induction update with
  | right => exact .right
  | left => exact .left
  | inLeft _ ih => exact .inLeft ih
  | inRight _ ih => exact .inRight ih

theorem update_size {s t : LabelledTree (Nat × Bounds)} (update : Update s t) :
    s.erase.size = t.erase.size := by
  induction update <;> simp only [LabelledTree.erase, Tree.size] at * <;> omega

/-- Every local interval-update rule preserves a canonical annotation. -/
theorem update_canonical {s t : LabelledTree (Nat × Bounds)} (update : Update s t)
    (lo : Nat) (canonical : s = label s.erase lo) : t = label t.erase lo := by
  induction update generalizing lo with
  | right a b c x y bx byBounds =>
    simp only [LabelledTree.erase, label, LabelledTree.node.injEq, Prod.mk.injEq] at canonical ⊢
    rcases canonical with ⟨⟨ha, hx, hb⟩, hy, hc⟩
    rcases hx with ⟨rfl, rfl⟩
    rcases hy with ⟨rfl, rfl⟩
    simp only [Tree.size, Nat.add_assoc] at ha hb hc ⊢
    exact ⟨ha, ⟨True.intro, True.intro⟩, hb, ⟨True.intro, True.intro⟩, hc⟩
  | left a b c x y bx byBounds =>
    simp only [LabelledTree.erase, label, LabelledTree.node.injEq, Prod.mk.injEq] at canonical ⊢
    rcases canonical with ⟨ha, hx, ⟨hb, hy, hc⟩⟩
    rcases hx with ⟨rfl, rfl⟩
    rcases hy with ⟨rfl, rfl⟩
    simp only [Tree.size, Nat.add_assoc] at ha hb hc ⊢
    exact ⟨⟨ha, ⟨True.intro, True.intro⟩, hb⟩, ⟨True.intro, True.intro⟩, hc⟩
  | @inLeft a b c entry update ih =>
    simp only [LabelledTree.erase, label, LabelledTree.node.injEq] at canonical ⊢
    obtain ⟨ha, hentry, hc⟩ := canonical
    have size := update_size update
    simpa only [Tree.size, ← size] using And.intro (ih lo ha) (And.intro hentry hc)
  | @inRight a b c entry update ih =>
    simp only [LabelledTree.erase, label, LabelledTree.node.injEq] at canonical ⊢
    obtain ⟨hc, hentry, ha⟩ := canonical
    have size := update_size update
    simpa only [Tree.size, ← size] using And.intro hc (And.intro hentry (ih _ ha))

end RotationBST.IntervalMetadata.Maintenance
