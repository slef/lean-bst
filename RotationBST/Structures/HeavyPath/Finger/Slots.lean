module

public import RotationBST.Structures.HeavyPath.Finger.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Recursive.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree PopTart.Chocolate

theorem sideSlots_nonempty {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (boundary : LabelledTree α) (carry : ℝ) (fs : List (Frame α)) :
    sideSlots weight payload boundary carry fs ≠ [] := by cases fs <;> simp [sideSlots]

theorem sideSlots_nonnegative {α : Type} {weight : α → ℝ} (payload : LabelledTree α → Tree)
    {boundary : LabelledTree α} (boundaryPositive : Positive weight boundary)
    {carry : ℝ} (carryNonnegative : 0 ≤ carry) {fs : List (Frame α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f) ∧ 0 < weight (frameKey f)) :
    ∀ entry ∈ sideSlots weight payload boundary carry fs, 0 ≤ entry.2 := by
  induction fs generalizing carry with
  | nil =>
    intro entry member
    simp only [sideSlots, List.mem_singleton] at member
    subst entry
    exact add_nonneg carryNonnegative (mass_nonnegative (positive_nonnegative boundaryPositive))
  | cons f fs ih =>
    have first := framesPositive f (by simp)
    intro entry member
    rcases List.mem_cons.mp member with rfl | later
    · exact add_nonneg carryNonnegative (mass_nonnegative (positive_nonnegative first.1))
    · exact ih first.2.le (fun g hg => framesPositive g (by simp [hg])) entry later

theorem sideSlots_mass {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (boundary : LabelledTree α) (carry : ℝ) (fs : List (Frame α)) :
    ((sideSlots weight payload boundary carry fs).map Prod.snd).sum =
      carry + HeavyPath.mass weight boundary + (fs.map (frameMass weight)).sum := by
  induction fs generalizing carry with
  | nil => simp [sideSlots]
  | cons f fs ih =>
    simp only [sideSlots, List.map_cons, List.sum_cons, ih]
    cases f <;> simp only [framePayload, frameKey, frameMass] <;> ring

theorem sideSlots_span {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (boundary : LabelledTree α) (carry : ℝ) (fs : List (Frame α)) :
    fringeSpan (sideSlots weight payload boundary carry fs) =
      (fs.map (fun f => (payload (framePayload f)).size + 1)).sum + (payload boundary).size + 1 := by
  induction fs generalizing carry with
  | nil => simp [sideSlots, fringeSpan]
  | cons f fs ih =>
    change (payload (framePayload f)).size + 1 +
      fringeSpan (sideSlots weight payload boundary (weight (frameKey f)) fs) = _
    rw [ih]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem frame_mass_partition {α : Type} (weight : α → ℝ) (cs : List (Frame α)) :
    ((lowerFrames cs).map (frameMass weight)).sum + ((upperFrames cs).map (frameMass weight)).sum =
      (cs.map (frameMass weight)).sum := by
  induction cs with
  | nil => simp [lowerFrames, upperFrames]
  | cons f cs ih =>
    cases f <;> simp only [lowerFrames, upperFrames, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil] <;> linarith

theorem reflectSlot_involutive (entry : Tree × ℝ) : reflectSlot (reflectSlot entry) = entry := by
  rcases entry with ⟨tree, weight⟩
  simp [reflectSlot, Tree.mirror_mirror]

theorem fringeSpan_reverse (slots : List (Tree × ℝ)) : fringeSpan slots.reverse = fringeSpan slots := by
  simp [fringeSpan, List.map_reverse]

theorem fringeSpan_reflect (slots : List (Tree × ℝ)) :
    fringeSpan (slots.map reflectSlot) = fringeSpan slots := by
  simp only [fringeSpan, List.map_map, Function.comp_def, reflectSlot, Tree.mirror_size]

end RotationBST.HeavyPath.Finger
