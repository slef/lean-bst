module

public import RotationBST.Models.Labelled.Cursor.Map.Definitions.Abstract
public import RotationBST.Models.Labelled.Cursor.Operational
public import RotationBST.Models.Labelled.Labelling
import Mathlib.Tactic

@[expose] public section
namespace RotationBST

theorem LabelledTree.erase_map {α β : Type} (f : α → β) (t : LabelledTree α) :
    (t.map f).erase = t.erase := by
  induction t <;> simp_all only [LabelledTree.map, LabelledTree.erase]

theorem LabelledTree.inorder_map {α β : Type} (f : α → β) (t : LabelledTree α) :
    (t.map f).inorder = t.inorder.map f := by
  induction t <;> simp_all only [LabelledTree.map, LabelledTree.inorder, List.map_nil,
    List.map_append, List.map_cons]

namespace LabelledCursor

theorem map_plug {α β : Type} (f : α → β) (cs : List (Frame α)) (t : LabelledTree α) :
    (plug cs t).map f = plug (cs.map (Frame.map f)) (t.map f) := by
  induction cs generalizing t with
  | nil => rfl
  | cons frame cs ih => cases frame <;> simp only [plug, ih, Frame.map, List.map_cons, LabelledTree.map]

theorem map_tree {α β : Type} (f : α → β) (c : Config α) :
    (c.map f).tree = c.tree.map f := (map_plug f c.context c.focus).symm

theorem map_erase {α β : Type} (f : α → β) (c : Config α) : (c.map f).erase = c.erase := by
  rcases c with ⟨focus, cs⟩
  simp only [Config.map, Config.erase, LabelledTree.erase_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro frame _
  cases frame <;> simp only [Frame.map, Frame.erase, LabelledTree.erase_map, Function.comp_apply]

theorem map_read {α β : Type} (f : α → β) (c : Config α) :
    (c.map f).read = c.read.map f := by
  rcases c with ⟨focus, cs⟩
  cases focus <;> rfl

theorem perform_map {α β : Type} (f : α → β) (op : Multifinger.Opcode) (c : Config α) :
    (perform op c).map (Config.map f) = perform op (c.map f) := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => cases op <;> rfl
  | node l entry r =>
    cases op with
    | downLeft => cases l <;> rfl
    | downRight => cases r <;> rfl
    | upLeft | upRight | rotateLeftChild | rotateRightChild =>
      cases cs with
      | nil => rfl
      | cons frame cs => cases frame <;> rfl

theorem plug_inorder {α : Type} (cs : List (Frame α)) {s t : LabelledTree α}
    (same : s.inorder = t.inorder) : (plug cs s).inorder = (plug cs t).inorder := by
  induction cs generalizing s t with
  | nil => exact same
  | cons frame cs ih =>
    cases frame <;> apply ih <;> simp only [LabelledTree.inorder, same]

/-- All six pointer primitives preserve the inorder list of stored entries. -/
theorem perform_inorder {α : Type} {op : Multifinger.Opcode} {s t : Config α}
    (execution : perform op s = some t) : s.tree.inorder = t.tree.inorder := by
  unfold perform at execution
  split at execution <;> simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst t
  all_goals simp only [Config.tree, plug]
  all_goals apply plug_inorder; simp only [LabelledTree.inorder, List.append_assoc, List.cons_append]

end LabelledCursor
end RotationBST
