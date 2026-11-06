module

public import RotationBST.Structures.HeavyPath.Finger.Build
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree

private theorem rebuilt_blocks_length {α : Type} {weight : α → ℝ}
    {cs : List (Frame α)} {focus : LabelledTree α}
    (positive : Positive weight (plug cs focus)) (fs : List (Frame α))
    (subset : ∀ f ∈ fs, f ∈ cs) :
    (fs.map (fun f => (rebuild weight (framePayload f)).size + 1)).sum =
        (fs.flatMap lowerBlock).length ∧
    (fs.map (fun f => (rebuild weight (framePayload f)).size + 1)).sum =
        (fs.flatMap upperBlock).length := by
  simp only [List.length_flatMap]
  constructor <;> congr 1 <;> apply List.map_congr_left <;> intro f hf
  · rw [(block_length f).1, rebuild_size (payload_positive cs focus positive (subset f hf))]
  · rw [(block_length f).2, rebuild_size (payload_positive cs focus positive (subset f hf))]

theorem build_side_sizes {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    (build weight cs left right).lower.decode.tree.mirror.size =
      ((lowerFrames cs).flatMap lowerBlock).length + left.erase.size ∧
    (build weight cs left right).upper.decode.tree.size =
      right.erase.size + ((upperFrames cs).flatMap upperBlock).length := by
  obtain ⟨_, lowerFringe, upperFringe⟩ := build_valid_fringe positive
  have focus := (context_positive cs (.node left key right) positive).1
  have lowerSpan := fringeSpan_fringe (build weight cs left right).lower.decode.mirror
  have upperSpan := fringeSpan_fringe (build weight cs left right).upper.decode
  rw [lowerFringe, sideSlots_span, WeightedTree.mirror_tree,
    (rebuilt_blocks_length positive (lowerFrames cs) (fun _ hf => lowerFrames_mem hf)).1,
    rebuild_size focus.1] at lowerSpan
  rw [upperFringe, fringeSpan_reverse, sideSlots_span, List.map_reverse, List.sum_reverse,
    (rebuilt_blocks_length positive (upperFrames cs) (fun _ hf => upperFrames_mem hf)).2,
    rebuild_size focus.2.2] at upperSpan
  constructor <;> omega

theorem build_size {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    (build weight cs left right).tree.size = (plug cs (.node left key right)).erase.size := by
  obtain ⟨lowerSize, upperSize⟩ := build_side_sizes positive
  have source := congrArg List.length (context_inorder cs (.node left key right))
  simp only [List.length_append, Representation.Bridge.inorder_length,
    LabelledTree.erase, Tree.size] at source
  change (build weight cs left right).lower.decode.tree.mirror.size + 1 +
    (build weight cs left right).upper.decode.tree.size = _
  omega

theorem lower_blocks_offset {α : Type} (cs : List (Frame α)) :
    ((lowerFrames cs).flatMap lowerBlock).length = Pointer.offset (cs.map Frame.erase) := by
  induction cs with
  | nil => rfl
  | cons f cs ih =>
    cases f <;> simp only [lowerFrames, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.length_append, List.map_cons,
      Frame.erase, Pointer.offset, ih, (block_length _).1, framePayload]; omega

/-- The represented root is exactly the original source finger rank. -/
theorem build_root_key {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    (Pointer.Config.mk (build weight cs left right).tree []).key? =
      (Config.mk (.node left key right) cs).erase.key? := by
  simp only [Pointer.Config.key?, Pair.tree, Pointer.offset, Config.erase,
    LabelledTree.erase, Nat.zero_add, (build_side_sizes positive).1, lower_blocks_offset]

theorem build_labels {α : Type} [Preorder α] {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right)))
    (ordered : (plug cs (.node left key right)).Ordered) :
    ∃! u : LabelledTree α, u.erase = (build weight cs left right).tree ∧
      u.inorder = (plug cs (.node left key right)).inorder ∧ u.Ordered := by
  apply Representation.ordered_labels_exist_unique
  · rw [Representation.Bridge.inorder_length, build_size positive]
  · exact (Representation.ordered_iff _).mp ordered

theorem build_initialization {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ cost, cost ≤ 16 * (plug cs (.node left key right)).erase.size ∧
      Pointer.Trace ⟨(plug cs (.node left key right)).erase, []⟩
        ⟨(build weight cs left right).tree, []⟩ cost := by
  exact Pointer.reshape _ _ (build_size positive).symm

end RotationBST.HeavyPath.Finger
