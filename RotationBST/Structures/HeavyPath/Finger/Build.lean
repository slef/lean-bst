module

public import RotationBST.Structures.HeavyPath.Finger.Assembly
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree PopTart.Chocolate

theorem build_valid_fringe {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    (build weight cs left right).Valid ∧
    (build weight cs left right).lower.decode.mirror.fringe =
      sideSlots weight (rebuild weight) left 0 (lowerFrames cs) ∧
    (build weight cs left right).upper.decode.fringe =
      (sideSlots weight (rebuild weight) right 0 (upperFrames cs).reverse).reverse := by
  have focus := (context_positive cs (.node left key right) positive).1
  have frames : ∀ f ∈ cs, Positive weight (framePayload f) ∧ 0 < weight (frameKey f) := by
    intro f hf
    exact ⟨payload_positive cs (.node left key right) positive hf,
      context_key_positive cs (.node left key right) positive hf⟩
  let lower := sideSlots weight (rebuild weight) left 0 (lowerFrames cs)
  let upper := sideSlots weight (rebuild weight) right 0 (upperFrames cs).reverse
  have lowerNonempty : lower ≠ [] := sideSlots_nonempty _ _ _ _ _
  have upperNonempty : upper ≠ [] := sideSlots_nonempty _ _ _ _ _
  have lowerNonnegative : ∀ entry ∈ lower, 0 ≤ entry.2 :=
    sideSlots_nonnegative _ focus.1 le_rfl (fun f hf => frames f (lowerFrames_mem hf))
  have upperNonnegative : ∀ entry ∈ upper, 0 ≤ entry.2 :=
    sideSlots_nonnegative _ focus.2.2 le_rfl (fun f hf => frames f (upperFrames_mem (List.mem_reverse.mp hf)))
  have lowerAssembled := assemble_valid_fringe (lower.map reflectSlot).reverse
    (by simpa using lowerNonempty) (by
      intro entry member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp member)
      exact lowerNonnegative original originalMember)
  have upperAssembled := assemble_valid_fringe upper.reverse
    (by simpa using upperNonempty) (fun entry member => upperNonnegative entry (List.mem_reverse.mp member))
  refine ⟨⟨lowerAssembled.1, upperAssembled.1⟩, ?_, upperAssembled.2⟩
  change (assemble (lower.map reflectSlot).reverse).decode.mirror.fringe = lower
  rw [WeightedTree.mirror_fringe, lowerAssembled.2]
  change (((lower.map reflectSlot).reverse).map reflectSlot).reverse = lower
  simp only [List.map_reverse, List.map_map, Function.comp_def, reflectSlot_involutive,
    List.reverse_reverse]
  exact List.map_id lower

/-- The finger's own weight is the only node weight outside the two stacks. -/
theorem build_mass {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    weight key + (build weight cs left right).mass = HeavyPath.mass weight (plug cs (.node left key right)) := by
  obtain ⟨_, lowerFringe, upperFringe⟩ := build_valid_fringe positive
  have lowerMass := WeightedTree.fringe_mass (build weight cs left right).lower.decode.mirror
  have upperMass := WeightedTree.fringe_mass (build weight cs left right).upper.decode
  rw [lowerFringe, WeightedTree.mirror_mass, sideSlots_mass] at lowerMass
  rw [upperFringe, List.map_reverse, List.sum_reverse, sideSlots_mass,
    List.map_reverse, List.sum_reverse] at upperMass
  rw [context_mass]
  change weight key + ((build weight cs left right).lower.decode.mass +
      (build weight cs left right).upper.decode.mass) =
    HeavyPath.mass weight left + weight key + HeavyPath.mass weight right + (cs.map (frameMass weight)).sum
  have partition := frame_mass_partition weight cs
  linarith

end RotationBST.HeavyPath.Finger
