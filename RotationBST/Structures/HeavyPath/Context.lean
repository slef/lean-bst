module

public import RotationBST.Structures.HeavyPath.Mass
public import RotationBST.Models.Labelled.Cursor.Abstract
public import RotationBST.Models.Pointer.Navigation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath
open LabelledCursor

theorem plug_append {α : Type} (cs ds : List (Frame α)) (t : LabelledTree α) :
    plug (cs ++ ds) t = plug ds (plug cs t) := by
  induction cs generalizing t with
  | nil => rfl
  | cons frame cs ih => cases frame <;> simp only [List.cons_append, plug, ih]

theorem extend_left_tree {α : Type} (cursor : Config α) (x : α) (r : LabelledTree α) :
    (extend cursor (.left x r)).tree = .node cursor.tree x r := by
  simp only [extend, Config.tree, plug_append, plug]

theorem extend_right_tree {α : Type} (cursor : Config α) (l : LabelledTree α) (x : α) :
    (extend cursor (.right l x)).tree = .node l x cursor.tree := by
  simp only [extend, Config.tree, plug_append, plug]

theorem solid_append {α : Type} (weight : α → ℝ) (cs ds : List (Frame α)) (t : LabelledTree α) :
    SolidContext weight t (cs ++ ds) ↔ SolidContext weight t cs ∧ SolidContext weight (plug cs t) ds := by
  induction cs generalizing t with
  | nil => simp [SolidContext, plug]
  | cons frame cs ih => cases frame <;> simp only [List.cons_append, SolidContext, plug, ih, and_assoc]

/-- Frame charges account for every original node exactly once. -/
theorem context_mass {α : Type} (weight : α → ℝ) (cs : List (Frame α)) (t : LabelledTree α) :
    mass weight (plug cs t) = mass weight t + (cs.map (frameMass weight)).sum := by
  induction cs generalizing t with
  | nil => simp [plug]
  | cons frame cs ih =>
    cases frame <;> simp only [plug, ih, mass, List.map_cons, List.sum_cons, frameMass] <;> ring

/-- Reuse the actual labelled cursor's erasure to descend to a nonempty focus.
No heavy-path comparison is counted as a free physical finger movement. -/
theorem cursor_trace {α : Type} (cursor : Config α) (nonempty : cursor.focus ≠ .nil) :
    Pointer.Trace ⟨cursor.tree.erase, []⟩ cursor.erase cursor.context.length := by
  have erased := LabelledCursor.Results.erase_tree cursor
  cases focus : cursor.focus with
  | nil => exact False.elim (nonempty focus)
  | node l x r =>
    have trace := Pointer.descend (cursor.context.map Frame.erase) l.erase r.erase
    rw [erased]
    simpa only [Config.erase, Pointer.Config.tree, focus, LabelledTree.erase, List.length_map] using trace

end RotationBST.HeavyPath
