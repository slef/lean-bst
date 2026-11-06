module

public import RotationBST.Structures.HeavyPath.Finger.Slots
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger
open PopTart PopTart.WeightedTree PopTart.Chocolate

private theorem base_valid (tree : Tree) {weight : ℝ} (nonnegative : 0 ≤ weight) :
    (Layer.last .zero (.base (.leaf tree weight))).Valid 0 := by
  exact ⟨trivial, ⟨.leaf tree weight, nonnegative⟩, fun _ => ⟨_, rfl⟩⟩

/-- Actual Chocolate assembly preserves every fringe occurrence and its charge. -/
theorem assemble_valid_fringe (slots : List (Tree × ℝ)) (nonempty : slots ≠ [])
    (nonnegative : ∀ entry ∈ slots, 0 ≤ entry.2) :
    (assemble slots).Valid 0 ∧ (assemble slots).decode.fringe = slots := by
  induction slots with
  | nil => exact False.elim (nonempty rfl)
  | cons entry rest ih =>
    cases rest with
    | nil => exact ⟨base_valid entry.1 (nonnegative entry (by simp)), rfl⟩
    | cons next rest =>
      obtain ⟨valid, fringe⟩ := ih (by simp) (fun e he => nonnegative e (by simp [he]))
      have result := Chocolate.Results.push valid (.leaf entry.1 entry.2)
        (nonnegative entry (by simp)) []
      exact ⟨result.1, by simp only [assemble, result.2.1, WeightedTree.fringe, fringe,
        List.singleton_append]⟩

theorem assemble_mass (slots : List (Tree × ℝ)) (nonempty : slots ≠ [])
    (nonnegative : ∀ entry ∈ slots, 0 ≤ entry.2) :
    (assemble slots).decode.mass = (slots.map Prod.snd).sum := by
  have h := WeightedTree.fringe_mass (assemble slots).decode
  rw [(assemble_valid_fringe slots nonempty nonnegative).2] at h
  exact h.symm

end RotationBST.HeavyPath.Finger
