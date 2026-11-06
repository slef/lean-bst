module

public import RotationBST.Structures.HeavyPath.Finger.History.Preservation
public import RotationBST.Structures.HeavyPath.Finger.Assembly
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History
open Paired Recursive LabelledCursor PopTart PopTart.Chocolate

/-- Fresh assembly uses one push per separator; opaque payload size does
not contribute to the outer stack's potential. -/
theorem assemble_potential (slots : List (Tree × ℝ)) (nonempty : slots ≠ [])
    (nonnegative : ∀ entry ∈ slots, 0 ≤ entry.2) :
    (assemble slots).potential ≤ 20 * (slots.length - 1) := by
  induction slots with
  | nil => exact False.elim (nonempty rfl)
  | cons entry rest ih =>
    cases rest with
    | nil => exact le_rfl
    | cons next rest =>
      have remaining : ∀ e ∈ next :: rest, 0 ≤ e.2 := fun e he => nonnegative e (by simp [he])
      have initial := (assemble_valid_fringe (next :: rest) (by simp) remaining).1
      have push := (Chocolate.Results.push initial (.leaf entry.1 entry.2)
        (nonnegative entry (by simp)) []).2.2.2.2
      have later := ih (by simp) remaining
      simp only [assemble, List.length_cons] at *
      omega

private theorem slots_length {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (boundary : LabelledTree α) (carry : ℝ) (fs : List (Frame α)) :
    (Finger.sideSlots weight payload boundary carry fs).length = fs.length + 1 := by
  induction fs generalizing carry with
  | nil => rfl
  | cons f fs ih => simp only [Finger.sideSlots, List.length_cons, ih]

private theorem side_lengths {α : Type} (cs : List (Frame α)) :
    (lowerFrames cs).length + (upperFrames cs).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons f cs ih =>
    cases f <;> simp only [lowerFrames, upperFrames, List.length_append,
      List.length_cons, List.length_nil] <;> omega

theorem canonical_pair_potential {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    (build weight cs left right).potential ≤ 20 * cs.length := by
  have focus := (context_positive cs (.node left key right) positive).1
  have frames : ∀ f ∈ cs, Positive weight (framePayload f) ∧ 0 < weight (frameKey f) := by
    intro f hf
    exact ⟨payload_positive cs _ positive hf, context_key_positive cs _ positive hf⟩
  let lower := Finger.sideSlots weight (rebuild weight) left 0 (lowerFrames cs)
  let upper := Finger.sideSlots weight (rebuild weight) right 0 (upperFrames cs).reverse
  have lowerNonempty : lower ≠ [] := Finger.sideSlots_nonempty _ _ _ _ _
  have upperNonempty : upper ≠ [] := Finger.sideSlots_nonempty _ _ _ _ _
  have lowerNonnegative : ∀ e ∈ lower, 0 ≤ e.2 :=
    Finger.sideSlots_nonnegative _ focus.1 le_rfl (fun f hf => frames f (lowerFrames_mem hf))
  have upperNonnegative : ∀ e ∈ upper, 0 ≤ e.2 :=
    Finger.sideSlots_nonnegative _ focus.2.2 le_rfl
      (fun f hf => frames f (upperFrames_mem (List.mem_reverse.mp hf)))
  have lowerBound := assemble_potential (lower.map reflectSlot).reverse
    (by simpa using lowerNonempty) (by
      intro e he
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
      exact lowerNonnegative old oldMember)
  have upperBound := assemble_potential upper.reverse (by simpa using upperNonempty)
    (fun e he => upperNonnegative e (List.mem_reverse.mp he))
  have lowerLength : lower.length = (lowerFrames cs).length + 1 := slots_length _ _ _ _ _
  have upperLength : upper.length = (upperFrames cs).length + 1 := by
    simp only [upper, slots_length, List.length_reverse]
  simp only [List.length_reverse, List.length_map, lowerLength, upperLength, Nat.add_sub_cancel] at lowerBound upperBound
  have total := side_lengths cs
  change (assemble (lower.map reflectSlot).reverse).potential + (assemble upper.reverse).potential ≤ _
  omega

end RotationBST.HeavyPath.Finger.History
