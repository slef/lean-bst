module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Definitions.Abstract
public import RotationBST.Models.Labelled.Cursor.Abstract
public import RotationBST.Models.Pointer.Keys
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Reverse
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Requests
open LabelledCursor

theorem source_append {α : Type} (c : Config α) (xs ys : List Multifinger.Opcode) :
    sourceRun c (xs ++ ys) = (sourceRun c xs).bind (fun next => sourceRun next ys) :=
  Simulation.source_append c xs ys

theorem source_size {α : Type} {c final : Config α} {ops : List Multifinger.Opcode}
    (legal : sourceRun c ops = some final) : c.tree.erase.size = final.tree.erase.size := by
  induction ops generalizing c with
  | nil => simp only [sourceRun, Option.some.injEq] at legal; subst final; rfl
  | cons op ops ih =>
    cases first : perform op c with
    | none => simp [sourceRun, first] at legal
    | some next =>
      have rest : sourceRun next ops = some final := by
        simpa only [sourceRun, first, Option.bind_some] using legal
      have stepSize := (LabelledCursor.Results.perform_physical first).size_eq
      rw [← LabelledCursor.Results.erase_tree c, ← LabelledCursor.Results.erase_tree next] at stepSize
      exact stepSize.trans (ih rest)

theorem Serves.legal {α : Type} {c final : Config α} {ops : List Multifinger.Opcode} {key : Nat}
    (search : Serves c ops key final) : sourceRun c ops = some final := by
  obtain ⟨before, after, visited, rfl, first, _, last⟩ := search
  simp only [source_append, first, Option.bind_some, last]

theorem config_nonempty {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) : c.focus ≠ .nil := by
  intro empty
  simp only [ConfigValid, empty] at valid

end RotationBST.HeavyPath.Finger.History.Simulation.Requests
