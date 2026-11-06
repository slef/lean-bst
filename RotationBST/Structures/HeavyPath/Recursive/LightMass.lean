module

public import RotationBST.Structures.HeavyPath.Recursive.Canonical
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive
open Paired LabelledCursor

theorem focus_mass_le {α : Type} {weight : α → ℝ} (cs : List (Frame α)) (t : LabelledTree α)
    (positive : Positive weight (plug cs t)) : mass weight t ≤ mass weight (plug cs t) := by
  have partition := context_mass weight cs t
  have charges := (context_positive cs t positive).2
  have nonnegative : 0 ≤ (cs.map (frameMass weight)).sum := by
    apply List.sum_nonneg
    intro value mem
    obtain ⟨frame, member, rfl⟩ := List.mem_map.mp mem
    exact (charges frame member).le
  linarith only [partition, nonnegative]

/-- Every off-path subtree of a solid context has at most half the total
source mass, even if it is attached far below the path's first node. -/
theorem solid_payload_half {α : Type} {weight : α → ℝ} (cs : List (Frame α)) (t : LabelledTree α)
    (solid : SolidContext weight t cs) (positive : Positive weight (plug cs t))
    {frame : Frame α} (mem : frame ∈ cs) :
    2 * mass weight (framePayload frame) ≤ mass weight (plug cs t) := by
  induction cs generalizing t with
  | nil => cases mem
  | cons head cs ih =>
    rcases List.mem_cons.mp mem with same | member
    · subst head
      cases frame with
      | left x r =>
        have parentPositive := (context_positive cs (.node t x r) positive).1
        have half := right_light_half (positive_nonnegative parentPositive) solid.1
        have outer := focus_mass_le cs (.node t x r) positive
        change 2 * mass weight r ≤ mass weight (plug cs (.node t x r))
        linarith only [half, outer]
      | right l x =>
        have parentPositive := (context_positive cs (.node l x t) positive).1
        have half := left_light_half (positive_nonnegative parentPositive) solid.1
        have outer := focus_mass_le cs (.node l x t) positive
        change 2 * mass weight l ≤ mass weight (plug cs (.node l x t))
        linarith only [half, outer]
    · cases head with
      | left x r => exact ih (.node t x r) solid.2 positive member
      | right l x => exact ih (.node l x t) solid.2 positive member

theorem extract_payload_half {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {frame : Frame α} (mem : frame ∈ (extract weight t).context) :
    2 * mass weight (framePayload frame) ≤ mass weight t := by
  have source : Positive weight (plug (extract weight t).context (extract weight t).focus) := by
    change Positive weight (extract weight t).tree
    rw [HeavyPath.Results.extract_tree]
    exact positive
  have half := solid_payload_half _ _ (HeavyPath.Results.extract_solid weight t) source mem
  change _ ≤ mass weight (extract weight t).tree at half
  simpa only [HeavyPath.Results.extract_tree] using half

theorem context_key_positive {α : Type} {weight : α → ℝ} (cs : List (Frame α)) (t : LabelledTree α)
    (positive : Positive weight (plug cs t)) {frame : Frame α} (mem : frame ∈ cs) :
    0 < weight (frameKey frame) := by
  induction cs generalizing t with
  | nil => cases mem
  | cons head cs ih =>
    rcases List.mem_cons.mp mem with same | member
    · subst head
      cases frame with
      | left x r => exact (context_positive cs (.node t x r) positive).1.2.1
      | right l x => exact (context_positive cs (.node l x t) positive).1.2.1
    · cases head with
      | left x r => exact ih (.node t x r) positive member
      | right l x => exact ih (.node l x t) positive member

/-- The frame charge pays for both its separator key and its recursive
payload. This is the bridge between pop-tart fringe weights and node weights. -/
theorem extract_charge_bounds {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {frame : Frame α} (mem : frame ∈ (extract weight t).context) :
    0 < weight (frameKey frame) ∧ weight (frameKey frame) ≤ frameMass weight frame ∧
      mass weight (framePayload frame) ≤ frameMass weight frame := by
  have source : Positive weight (plug (extract weight t).context (extract weight t).focus) := by
    change Positive weight (extract weight t).tree
    rw [HeavyPath.Results.extract_tree]
    exact positive
  have key := context_key_positive _ _ source mem
  have payload := mass_nonnegative (positive_nonnegative (extract_payload_positive positive mem))
  cases frame <;> simp only [frameKey, framePayload, frameMass] at * <;> exact ⟨key, by linarith, by linarith⟩

end RotationBST.HeavyPath.Recursive
