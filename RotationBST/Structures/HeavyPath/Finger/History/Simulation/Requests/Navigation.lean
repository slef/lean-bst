module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Source
public import RotationBST.Models.Multifinger.Program.Replay.Abstract
public import RotationBST.Models.Pointer.Search
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Requests
open LabelledCursor

/-- Labelled source execution is exactly the existing persistent-pointer
opcode semantics after erasing node entries. -/
theorem source_erase {α : Type} (c : Config α) (ops : List Multifinger.Opcode) :
    (sourceRun c ops).map Config.erase = Multifinger.replay ops c.erase := by
  induction ops generalizing c with
  | nil => rfl
  | cons op ops ih =>
    have first := LabelledCursor.Results.perform_erase op c
    cases eq : perform op c with
    | none =>
      simp only [eq, Option.map_none] at first
      simp only [sourceRun, Multifinger.replay, eq, ← first, Option.bind_none, Option.map_none]
    | some next =>
      simp only [eq, Option.map_some] at first
      simp only [sourceRun, Multifinger.replay, eq, ← first, Option.bind_some]
      exact ih next

/-- Every valid source rank admits a search: return to the root, then descend
to that rank. No additional hypothesis about an input algorithm is required. -/
theorem serves_exists {α : Type} (c : Config α) (key : Nat)
    (nonempty : c.focus ≠ .nil) (validKey : key < c.tree.erase.size) :
    ∃ result : List Multifinger.Opcode × Config α, Serves c result.1 key result.2 := by
  obtain ⟨visited, _, visitedKey, descend, _⟩ := Pointer.search_walk c.tree.erase key validKey
  have ascend : Pointer.Trace c.erase ⟨c.tree.erase, []⟩ c.context.length := by
    rcases c with ⟨focus, cs⟩
    cases focus with
    | nil => exact False.elim (nonempty rfl)
    | node l x r =>
      have physical := Pointer.ascend (cs.map Frame.erase) l.erase r.erase
      rw [LabelledCursor.Results.erase_tree]
      simpa only [Config.erase, LabelledTree.erase, Pointer.Config.tree, List.length_map] using physical
  obtain ⟨ops, _, replay⟩ := Multifinger.Replay.Results.record (ascend.append descend)
  have erased : (sourceRun c ops).map Config.erase = some visited := (source_erase c ops).trans replay
  cases eq : sourceRun c ops with
  | none => simp [eq] at erased
  | some final =>
    have finalEq : final.erase = visited := by simpa only [eq, Option.map_some, Option.some.injEq] using erased
    exact ⟨(ops, final), ops, [], final, by simp, eq, by rw [finalEq]; exact visitedKey, rfl⟩

/-- The source algorithm interface is inhabited by ordinary navigation. -/
theorem algorithm_exists (α : Type) : Nonempty (Algorithm α) := by
  classical
  let next : Config α → Nat → List Multifinger.Opcode × Config α := fun c key =>
    if h : c.focus ≠ .nil ∧ key < c.tree.erase.size then
      Classical.choose (serves_exists c key h.1 h.2)
    else ([], c)
  refine ⟨⟨fun _ c key => next c key, ?_⟩⟩
  intro past c key nonempty validKey
  have h : c.focus ≠ .nil ∧ key < c.tree.erase.size := ⟨nonempty, validKey⟩
  simp only [next, dite_eq_left h]
  exact Classical.choose_spec (serves_exists c key h.1 h.2)

end RotationBST.HeavyPath.Finger.History.Simulation.Requests
