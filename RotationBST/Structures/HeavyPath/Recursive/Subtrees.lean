module

public import RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive
open Paired LabelledCursor

theorem focus_size_le {α : Type} (cs : List (Frame α)) (t : LabelledTree α) :
    t.erase.size ≤ (plug cs t).erase.size := by
  induction cs generalizing t with
  | nil => exact le_rfl
  | cons frame cs ih =>
    cases frame with
    | left x r =>
      have parent := ih (.node t x r)
      simp only [plug, LabelledTree.erase, Tree.size] at *
      omega
    | right l x =>
      have parent := ih (.node l x t)
      simp only [plug, LabelledTree.erase, Tree.size] at *
      omega

theorem payload_size_lt {α : Type} (cs : List (Frame α)) (t : LabelledTree α)
    {frame : Frame α} (mem : frame ∈ cs) :
    (framePayload frame).erase.size < (plug cs t).erase.size := by
  induction cs generalizing t with
  | nil => cases mem
  | cons head cs ih =>
    rcases List.mem_cons.mp mem with same | member
    · subst head
      cases frame with
      | left x r =>
        have parent := focus_size_le cs (.node t x r)
        simp only [framePayload, plug, LabelledTree.erase, Tree.size] at *
        omega
      | right l x =>
        have parent := focus_size_le cs (.node l x t)
        simp only [framePayload, plug, LabelledTree.erase, Tree.size] at *
        omega
    · cases head with
      | left x r => exact ih (.node t x r) member
      | right l x => exact ih (.node l x t) member

theorem payload_positive {α : Type} {weight : α → ℝ} (cs : List (Frame α)) (t : LabelledTree α)
    (positive : Positive weight (plug cs t)) {frame : Frame α} (mem : frame ∈ cs) :
    Positive weight (framePayload frame) := by
  induction cs generalizing t with
  | nil => cases mem
  | cons head cs ih =>
    rcases List.mem_cons.mp mem with same | member
    · subst head
      cases frame with
      | left x r => exact (context_positive cs (.node t x r) positive).1.2.2
      | right l x => exact (context_positive cs (.node l x t) positive).1.1
    · cases head with
      | left x r => exact ih (.node t x r) positive member
      | right l x => exact ih (.node l x t) positive member

theorem extract_payload_size {α : Type} (weight : α → ℝ) (t : LabelledTree α)
    {frame : Frame α} (mem : frame ∈ (extract weight t).context) :
    (framePayload frame).erase.size < t.erase.size := by
  have bound := payload_size_lt (extract weight t).context (extract weight t).focus mem
  change (framePayload frame).erase.size < (extract weight t).tree.erase.size at bound
  simpa only [HeavyPath.Results.extract_tree] using bound

theorem extract_payload_positive {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {frame : Frame α} (mem : frame ∈ (extract weight t).context) :
    Positive weight (framePayload frame) := by
  apply payload_positive (extract weight t).context (extract weight t).focus _ mem
  change Positive weight (extract weight t).tree
  rw [HeavyPath.Results.extract_tree]
  exact positive

end RotationBST.HeavyPath.Recursive
