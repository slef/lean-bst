module

public import RotationBST.Structures.HeavyPath.Finger.History.Slots
public import RotationBST.Structures.HeavyPath.Finger.Preservation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree Recursive.History

theorem state_mass {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α} (valid : Valid weight cs left key right s) :
    weight key + s.pair.mass = HeavyPath.mass weight (plug cs (.node left key right)) := by
  have lowerMass := WeightedTree.fringe_mass s.pair.lower.decode.mirror
  have upperMass := WeightedTree.fringe_mass s.pair.upper.decode
  rw [valid.lower, WeightedTree.mirror_mass, sideSlots_mass] at lowerMass
  rw [valid.upper, List.map_reverse, List.sum_reverse, sideSlots_mass,
    List.map_reverse, List.sum_reverse] at upperMass
  rw [HeavyPath.context_mass, ← valid.context, List.map_map]
  change weight key + (s.pair.lower.decode.mass + s.pair.upper.decode.mass) =
    HeavyPath.mass weight left + weight key + HeavyPath.mass weight right +
      (s.ancestors.map (fun e => frameMass weight e.source)).sum
  have partition := split_sum (fun e => frameMass weight e.source) s.ancestors
  linarith

theorem state_side_sizes {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α} (valid : Valid weight cs left key right s) :
    s.pair.lower.decode.tree.mirror.size =
      ((Recursive.History.lower s.ancestors).flatMap Entry.lowerBlock).length + left.erase.size ∧
    s.pair.upper.decode.tree.size =
      right.erase.size + ((Recursive.History.upper s.ancestors).flatMap Entry.upperBlock).length := by
  have lowerSpan := fringeSpan_fringe s.pair.lower.decode.mirror
  have upperSpan := fringeSpan_fringe s.pair.upper.decode
  rw [valid.lower, (sideSlots_lengths valid.leftLayout 0 (fun e he => valid.children e (lower_mem he))).1,
    mirror_tree, List.length_append, Representation.Bridge.inorder_length] at lowerSpan
  rw [valid.upper, fringeSpan_reverse,
    (sideSlots_lengths valid.rightLayout 0 (fun e he => valid.children e (upper_mem (List.mem_reverse.mp he)))).2,
    List.reverse_reverse, List.length_append, Representation.Bridge.inorder_length] at upperSpan
  constructor <;> omega

theorem state_size {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α} (valid : Valid weight cs left key right s) :
    s.pair.tree.size = (plug cs (.node left key right)).erase.size := by
  obtain ⟨lowerSize, upperSize⟩ := state_side_sizes valid
  have source := congrArg List.length (context_inorder valid.context (.node left key right))
  simp only [List.length_append, Representation.Bridge.inorder_length,
    LabelledTree.erase, Tree.size] at source
  change s.pair.lower.decode.tree.mirror.size + 1 + s.pair.upper.decode.tree.size = _
  omega

theorem state_root_key {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α} (valid : Valid weight cs left key right s) :
    (Pointer.Config.mk s.pair.tree []).key? = (Config.mk (.node left key right) cs).erase.key? := by
  have lower : ((Recursive.History.lower s.ancestors).flatMap Entry.lowerBlock).length =
      Pointer.offset (cs.map Frame.erase) := by
    have original := lower_blocks_offset cs
    rw [← valid.context, ← lower_sources] at original
    change ((Recursive.History.lower s.ancestors).flatMap (fun e => Recursive.lowerBlock e.source)).length = _
    simpa only [valid.context, List.flatMap_map, Function.comp_def] using original
  simp only [Pointer.Config.key?, Pair.tree, Pointer.offset, Config.erase,
    LabelledTree.erase, Nat.zero_add, (state_side_sizes valid).1, lower]

theorem state_labels {α : Type} [Preorder α] {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α} {s : State α} (valid : Valid weight cs left key right s)
    (ordered : (plug cs (.node left key right)).Ordered) :
    ∃! u : LabelledTree α, u.erase = s.pair.tree ∧
      u.inorder = (plug cs (.node left key right)).inorder ∧ u.Ordered := by
  apply Representation.ordered_labels_exist_unique
  · rw [Representation.Bridge.inorder_length, state_size valid]
  · exact (Representation.ordered_iff _).mp ordered

end RotationBST.HeavyPath.Finger.History
