module

import RotationBST.Audit.Check
public import RotationBST.Models.Labelled.Cursor.AbstractBridge

@[expose] public section
namespace RotationBST.LabelledCursor.Results

theorem erase_tree {α : Type} (c : Config α) : c.tree.erase = c.erase.tree :=
  RotationBST.LabelledCursor.erase_tree c

theorem perform_erase {α : Type} (op : Multifinger.Opcode) (c : Config α) :
    (perform op c).map Config.erase = Multifinger.perform op c.erase :=
  RotationBST.LabelledCursor.perform_erase op c

theorem perform_physical {α : Type} {op : Multifinger.Opcode} {s t : Config α}
    (step : perform op s = some t) : Pointer.Step s.erase t.erase :=
  RotationBST.LabelledCursor.perform_physical step

theorem write_erase {α : Type} {s t : Config α} {entry : α}
    (write : s.write entry = some t) : t.erase = s.erase :=
  RotationBST.LabelledCursor.write_erase write

/-- Projecting node fields does not change the physical cursor. -/
theorem map_erase {α β : Type} (f : α → β) (c : Config α) : (c.map f).erase = c.erase :=
  LabelledCursor.map_erase f c

/-- Field projections commute with every pointer primitive. -/
theorem perform_map {α β : Type} (f : α → β) (op : Multifinger.Opcode) (c : Config α) :
    (perform op c).map (Config.map f) = perform op (c.map f) :=
  LabelledCursor.perform_map f op c

/-- Lift an already identified shape cursor to its labelled-tree view. -/
theorem lift {α : Type} (cursor : Pointer.Config) (whole : LabelledTree α)
    (shape : whole.erase = cursor.tree) :
    ∃ c : Config α, c.tree = whole ∧ c.erase = cursor := lift_config cursor whole shape

/-- Lift an exact labelled cursor through any field projection. -/
theorem lift_map {α β : Type} (f : α → β) (cursor : Config β) (whole : LabelledTree α)
    (mapped : whole.map f = cursor.tree) :
    ∃ c : Config α, c.tree = whole ∧ c.map f = cursor :=
  LabelledCursor.lift_map f cursor whole mapped

end RotationBST.LabelledCursor.Results

/-- info: abstract audit passed for `RotationBST.LabelledCursor.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.LabelledCursor.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Map.Definitions.Abstract]
