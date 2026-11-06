module

public import RotationBST.Models.Labelled.Cursor.Map.Basic

@[expose] public section
namespace RotationBST.LabelledCursor

/-- Lift an existing shape cursor to its view of a given labelled tree.
This is a representation witness, not a search or a runtime cursor move. -/
theorem lift_context {α : Type} (cs : List Pointer.Frame) (focus : Tree) (whole : LabelledTree α)
    (shape : whole.erase = Pointer.plug cs focus) :
    ∃ c : Config α, c.tree = whole ∧ c.erase = ⟨focus, cs⟩ := by
  induction cs generalizing focus with
  | nil => exact ⟨⟨whole, []⟩, rfl, by simp only [Config.erase, List.map_nil, Pointer.plug] at *; rw [shape]⟩
  | cons frame cs ih =>
    cases frame with
    | left r =>
      obtain ⟨⟨parent, path⟩, tree, erased⟩ := ih (.node focus r) shape
      have focused := congrArg Pointer.Config.focus erased
      have context := congrArg Pointer.Config.context erased
      cases parent with
      | nil => cases focused
      | node l entry right =>
        obtain ⟨hl, hr⟩ := Tree.node.inj focused
        refine ⟨⟨l, .left entry right :: path⟩, tree, ?_⟩
        simp only [Config.erase, List.map_cons, Frame.erase, hl, hr]
        exact congrArg (fun path => Pointer.Config.mk focus (.left r :: path)) context
    | right l =>
      obtain ⟨⟨parent, path⟩, tree, erased⟩ := ih (.node l focus) shape
      have focused := congrArg Pointer.Config.focus erased
      have context := congrArg Pointer.Config.context erased
      cases parent with
      | nil => cases focused
      | node left entry r =>
        obtain ⟨hl, hr⟩ := Tree.node.inj focused
        refine ⟨⟨r, .right left entry :: path⟩, tree, ?_⟩
        simp only [Config.erase, List.map_cons, Frame.erase, hl, hr]
        exact congrArg (fun path => Pointer.Config.mk focus (.right l :: path)) context

theorem lift_config {α : Type} (cursor : Pointer.Config) (whole : LabelledTree α)
    (shape : whole.erase = cursor.tree) :
    ∃ c : Config α, c.tree = whole ∧ c.erase = cursor :=
  lift_context cursor.context cursor.focus whole shape

/-- Lift a view through an arbitrary field projection, recovering its exact
labels and context. The lift is a proof witness, not a runtime traversal. -/
theorem lift_map {α β : Type} (f : α → β) (cursor : Config β) (whole : LabelledTree α)
    (mapped : whole.map f = cursor.tree) :
    ∃ c : Config α, c.tree = whole ∧ c.map f = cursor := by
  rcases cursor with ⟨focus, cs⟩
  induction cs generalizing focus whole with
  | nil =>
    exact ⟨⟨whole, []⟩, rfl, congrArg (fun t => Config.mk t []) mapped⟩
  | cons frame cs ih =>
    cases frame with
    | left entry right =>
      obtain ⟨⟨parent, path⟩, tree, projected⟩ := ih whole (.node focus entry right) mapped
      have focused := congrArg Config.focus projected
      have context := congrArg Config.context projected
      cases parent with
      | nil => cases focused
      | node l address r =>
        obtain ⟨hl, he, hr⟩ := LabelledTree.node.inj focused
        refine ⟨⟨l, .left address r :: path⟩, tree, ?_⟩
        simp only [Config.map, List.map_cons, Frame.map, hl, he, hr]
        exact congrArg (fun p => Config.mk focus (.left entry right :: p)) context
    | right left entry =>
      obtain ⟨⟨parent, path⟩, tree, projected⟩ := ih whole (.node left entry focus) mapped
      have focused := congrArg Config.focus projected
      have context := congrArg Config.context projected
      cases parent with
      | nil => cases focused
      | node l address r =>
        obtain ⟨hl, he, hr⟩ := LabelledTree.node.inj focused
        refine ⟨⟨r, .right l address :: path⟩, tree, ?_⟩
        simp only [Config.map, List.map_cons, Frame.map, hl, he, hr]
        exact congrArg (fun p => Config.mk focus (.right left entry :: p)) context

end RotationBST.LabelledCursor
