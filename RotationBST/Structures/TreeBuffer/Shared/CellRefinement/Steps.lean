module

public import RotationBST.Structures.TreeBuffer.Shared.CellRefinement.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Shared.Execution

@[expose] public section
namespace RotationBST.TreeBuffer.Shared

theorem Step.write_shape {α : Type} {fingers : Nat} {s t : State α fingers} {i : Fin fingers}
    {key : Nat} {value : α} {cost : Nat} (operation : Step s i t (some (.write key value)) cost) :
    t.tree.erase = s.tree.erase := by
  cases operation with
  | write value view execution =>
    simpa only [LabelledCursor.erase_tree, ← view.1] using
      congrArg Pointer.Config.tree (Nodes.write_shape execution)

namespace CellRefinement

/-- A rotation-free cell step has exactly the same event in the shared model.
Navigation charges four; reading or writing the current cell charges one. -/
theorem step {α : Type} {fingers : Nat} {s t : Cells.State α} {event : Option (Cells.Event α)}
    {work rotations : Nat} (operation : Cells.Step s t event work rotations) (zero : rotations = 0)
    (valid : s.scan.Valid) (actual : Shared.State α fingers) (i : Fin fingers)
    (represented : Represents actual s i) :
    ∃ final cost, Shared.Step actual i final event cost ∧ Represents final t i ∧ cost ≤ 4 * work := by
  cases operation with
  | @navigate a b y tree move key next pending closer =>
    obtain ⟨final, action, shape, positions⟩ := Shared.navigate_matching actual s.data represented.1 i a b s.scan.target y
      (tree.trans represented.2.1.symm) (by simpa only [represented.2.2] using key) move next
      (by rw [represented.2.1]; exact Scan.target_valid s.scan valid pending)
      (by simpa only [represented.2.1, represented.2.2] using closer)
    refine ⟨final, 4, action, ?_, by decide⟩
    exact ⟨action.valid s.data represented.1, shape, by simp only [positions, Function.update_self]⟩
  | read present pending arrived =>
    have action : Shared.Step actual i actual (some (.read s.scan.position (s.data s.scan.position))) 1 := by
      simpa only [represented.2.2] using Shared.read_exists actual s.data represented.1 i
    exact ⟨actual, 1, action, represented, by decide⟩
  | write value present pending arrived =>
    obtain ⟨final, action, positions⟩ := Shared.write_exists actual s.data represented.1 i value
    have action' : Shared.Step actual i final (some (.write s.scan.position value)) 1 := by
      simpa only [represented.2.2] using action
    refine ⟨final, 1, action', ?_, by decide⟩
    refine ⟨action'.valid s.data represented.1, action'.write_shape.trans represented.2.1, ?_⟩
    simpa only [positions, Scan.State.afterVisit] using represented.2.2
  | rotate _ => contradiction

end CellRefinement
end RotationBST.TreeBuffer.Shared
