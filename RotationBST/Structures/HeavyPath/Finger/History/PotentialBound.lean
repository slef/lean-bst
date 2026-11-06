module

public import RotationBST.Structures.HeavyPath.Recursive.History.PotentialBound
public import RotationBST.Structures.HeavyPath.Finger.History.Preservation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History
open Paired LabelledCursor Recursive Recursive.History PopTart

theorem sideSlots_length {α : Type} (weight : α → ℝ) (boundary : LabelledTree α)
    (shape : Tree) (carry : ℝ) (es : List (Entry α)) :
    (sideSlots weight boundary shape carry es).length = es.length + 1 := by
  induction es generalizing carry with
  | nil => rfl
  | cons e es ih => simp only [sideSlots, List.length_cons, ih]

theorem pair_potential_bound {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α}
    (valid : Valid weight cs left key right s) : s.pair.potential ≤ 20 * s.ancestors.length := by
  have lo := congrArg List.length valid.lower
  have hi := congrArg List.length valid.upper
  simp only [WeightedTree.mirror_fringe, List.length_reverse, List.length_map, sideSlots_length] at lo hi
  have lower := Chocolate.layer_potential_fringe s.pair.lower
  have upper := Chocolate.layer_potential_fringe s.pair.upper
  rw [lo] at lower
  rw [hi] at upper
  have lengths := Recursive.History.split_lengths s.ancestors
  simp only [Pair.potential]
  omega

/-- Uniform stored credit for arbitrary valid histories, including payload
occurrences and frozen metadata. This is not limited to freshly built states. -/
theorem potential_bound {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α}
    (valid : Valid weight cs left key right s) :
    s.potential + 20 ≤ 20 * (plug cs (.node left key right)).erase.size := by
  have outer := pair_potential_bound valid
  have lower := layout_potential_bound valid.leftLayout
  have upper := layout_potential_bound valid.rightLayout
  have inner := entry_credit_sum s.ancestors 20 (fun e member => layout_potential_bound (valid.children e member))
  have partition := context_size α cs (.node left key right)
  rw [← valid.context] at partition
  simp only [List.length_map, List.map_map, Function.comp_def, LabelledTree.erase, Tree.size] at partition
  simp only [State.potential]
  rw [← valid.context]
  omega

end RotationBST.HeavyPath.Finger.History
