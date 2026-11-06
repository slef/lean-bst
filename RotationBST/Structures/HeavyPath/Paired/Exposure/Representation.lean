module

public import RotationBST.Structures.HeavyPath.Paired.Exposure.Trace
public import RotationBST.Structures.HeavyPath.Paired.Substitution.Abstract
public import RotationBST.Structures.HeavyPath.Paired.Abstract
public import RotationBST.Structures.PopTart.Located.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired.Exposure
open PopTart PopTart.Chocolate LabelledCursor

theorem lowerSlots_append {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (cs ds : List (Frame α)) :
    lowerSlotsWith weight payload (cs ++ ds) = lowerSlotsWith weight payload cs ++ lowerSlotsWith weight payload ds := by
  induction cs with
  | nil => rfl
  | cons frame cs ih => cases frame <;> simp [lowerSlotsWith, ih]

theorem upperSlots_append {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (cs ds : List (Frame α)) :
    upperSlotsWith weight payload (cs ++ ds) = upperSlotsWith weight payload cs ++ upperSlotsWith weight payload ds := by
  induction cs with
  | nil => rfl
  | cons frame cs ih => cases frame <;> simp [upperSlotsWith, ih]

theorem empty_represents {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) :
    Stacks.empty.Represents weight payload [] :=
  ⟨Paired.Results.empty_valid, rfl, rfl⟩

theorem push_represents {α : Type} {weight : α → ℝ} {payload : LabelledTree α → Tree}
    {cs : List (Frame α)} {p : Stacks} (represented : p.Represents weight payload cs)
    (frame : Frame α) (nonnegative : 0 ≤ frameMass weight frame) :
    (p.pushWith weight payload frame).Represents weight payload (cs ++ [frame]) := by
  refine ⟨Substitution.Results.pushWith_valid payload represented.1 nonnegative, ?_, ?_⟩
  all_goals cases frame with
  | left x r =>
    have pushed := (Chocolate.Results.push represented.1.2 (.leaf (payload r).mirror _) nonnegative []).2.1
    simp only [frameMass] at pushed
    simp only [Stacks.pushWith, lowerSlots_append, upperSlots_append, lowerSlotsWith,
      upperSlotsWith, List.append_nil, List.reverse_append, List.reverse_singleton,
      List.nil_append, List.cons_append, WeightedTree.fringe, pushed, represented.2.1, represented.2.2]
  | right l x =>
    have pushed := (Chocolate.Results.push represented.1.1 (.leaf (payload l) _) nonnegative []).2.1
    simp only [frameMass] at pushed
    simp only [Stacks.pushWith, lowerSlots_append, upperSlots_append, lowerSlotsWith,
      upperSlotsWith, List.append_nil, List.reverse_append, List.reverse_singleton,
      List.nil_append, List.cons_append, WeightedTree.fringe, pushed, represented.2.1, represented.2.2]

theorem build_represents {α : Type} {weight : α → ℝ} (payload : LabelledTree α → Tree)
    (cs : List (Frame α)) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.buildWith weight payload cs Stacks.empty).Represents weight payload cs := by
  have general : ∀ (ds : List (Frame α)) (p : Stacks), p.Represents weight payload ds →
      (Stacks.buildWith weight payload cs p).Represents weight payload (ds ++ cs) := by
    induction cs with
    | nil => intro ds p represented; simpa [Stacks.buildWith] using represented
    | cons frame cs ih =>
      intro ds p represented
      have next := push_represents represented frame (nonnegative frame (by simp))
      have result := ih (by intro f hf; exact nonnegative f (by simp [hf]))
        (ds ++ [frame]) (p.pushWith weight payload frame) next
      simpa only [Stacks.buildWith, List.append_assoc, List.singleton_append] using result
  simpa using general [] Stacks.empty (empty_represents weight payload)

end RotationBST.HeavyPath.Paired.Exposure
