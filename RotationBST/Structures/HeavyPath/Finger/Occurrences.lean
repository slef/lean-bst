module

public import RotationBST.Structures.HeavyPath.Finger.DepthStep
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree

theorem sideSlots_head {α : Type} {weight : α → ℝ} {boundary : LabelledTree α}
    (boundaryPositive : Positive weight boundary) (carry : ℝ) {fs : List (Frame α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f) ∧ 0 < weight (frameKey f)) :
    ∃ subtree rest, Positive weight subtree ∧
      sideSlots weight (rebuild weight) boundary carry fs =
        (rebuild weight subtree, carry + HeavyPath.mass weight subtree) :: rest := by
  cases fs with
  | nil => exact ⟨boundary, [], boundaryPositive, rfl⟩
  | cons f fs => exact ⟨framePayload f, _, (framesPositive f (by simp)).1, rfl⟩

theorem sideSlots_lengths {α : Type} {weight : α → ℝ} {boundary : LabelledTree α}
    (boundaryPositive : Positive weight boundary) (carry : ℝ) {fs : List (Frame α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f) ∧ 0 < weight (frameKey f)) :
    fringeSpan (sideSlots weight (rebuild weight) boundary carry fs) =
        (fs.flatMap lowerBlock ++ boundary.inorder).length + 1 ∧
    fringeSpan (sideSlots weight (rebuild weight) boundary carry fs) =
        (boundary.inorder ++ fs.reverse.flatMap upperBlock).length + 1 := by
  have lower : fs.map (fun f => (rebuild weight (framePayload f)).size + 1) =
      fs.map (fun f => (lowerBlock f).length) := by
    apply List.map_congr_left
    intro f hf
    rw [rebuild_size (framesPositive f hf).1, (block_length f).1]
  have upper : fs.map (fun f => (rebuild weight (framePayload f)).size + 1) =
      fs.map (fun f => (upperBlock f).length) := by
    apply List.map_congr_left
    intro f hf
    rw [rebuild_size (framesPositive f hf).1, (block_length f).2]
  have boundarySize : (rebuild weight boundary).size = boundary.inorder.length := by
    rw [rebuild_size boundaryPositive, Representation.Bridge.inorder_length]
  constructor
  · simp only [List.length_append, List.length_flatMap]
    rw [sideSlots_span, lower, boundarySize]
  · simp only [List.length_append, List.length_flatMap, List.map_reverse, List.sum_reverse]
    rw [sideSlots_span, upper, boundarySize]
    omega

private theorem fringe_successor {tree : WeightedTree} {before after : List (Tree × ℝ)}
    {subtree : Tree} {charge : ℝ} (split : tree.fringe = before ++ (subtree, charge) :: after)
    (nonempty : after ≠ []) : fringeSpan before + subtree.size < tree.tree.size := by
  have total := fringeSpan_fringe tree
  rw [split, fringeSpan_append] at total
  change fringeSpan before + (subtree.size + 1 + fringeSpan after) = tree.tree.size + 1 at total
  have positive : 0 < fringeSpan after := by
    cases after with
    | nil => exact False.elim (nonempty rfl)
    | cons entry rest => change 0 < entry.1.size + 1 + fringeSpan rest; omega
  omega

/-- The incoming ancestor is charged to the first slot toward the finger,
so it is the predecessor of that slot in the lower physical orientation. -/
theorem side_predecessor_bound {α : Type} {weight : α → ℝ} {p : Pair} (valid : p.Valid)
    {whole : ℝ} (sourceMass : p.mass ≤ whole) {boundary : LabelledTree α}
    (boundaryPositive : Positive weight boundary) {key : α} (keyPositive : 0 < weight key)
    {fs : List (Frame α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f) ∧ 0 < weight (frameKey f))
    {before after : List (Tree × ℝ)}
    (split : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
      before ++ sideSlots weight (rebuild weight) boundary (weight key) fs ++ after)
    (existsKey : 0 < fringeSpan before) :
    (Tree.depth p.tree (fringeSpan before - 1) : ℝ) ≤
      15 + 15 * Real.logb 2 (whole / weight key) := by
  obtain ⟨subtree, rest, positive, head⟩ := sideSlots_head boundaryPositive (weight key) framesPositive
  have headSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
      before ++ (rebuild weight subtree, weight key + HeavyPath.mass weight subtree) :: (rest ++ after) := by
    simpa only [head, List.append_assoc, List.cons_append] using split
  obtain ⟨depth, slot⟩ := locate_split headSplit
  have charged : weight key ≤ weight key + HeavyPath.mass weight subtree := by
    have mass := HeavyPath.mass_nonnegative (positive_nonnegative positive)
    linarith
  exact separator_estimate keyPositive charged (located_mass valid slot).2 sourceMass
    (located_predecessor_bound valid slot (lt_of_lt_of_le keyPositive charged) existsKey)

/-- In the reversed upper fringe the same charged slot is last, and its
incoming ancestor is the successor immediately outside that fringe. -/
theorem side_successor_bound {α : Type} {weight : α → ℝ} {p : Pair} (valid : p.Valid)
    {whole : ℝ} (sourceMass : p.mass ≤ whole) {boundary : LabelledTree α}
    (boundaryPositive : Positive weight boundary) {key : α} (keyPositive : 0 < weight key)
    {fs : List (Frame α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f) ∧ 0 < weight (frameKey f))
    {before after : List (Tree × ℝ)}
    (split : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
      before ++ (sideSlots weight (rebuild weight) boundary (weight key) fs).reverse ++ after)
    (nonempty : after ≠ []) :
    (Tree.depth p.tree
      (fringeSpan before + fringeSpan (sideSlots weight (rebuild weight) boundary (weight key) fs) - 1) : ℝ) ≤
      15 + 15 * Real.logb 2 (whole / weight key) := by
  obtain ⟨subtree, rest, positive, head⟩ := sideSlots_head boundaryPositive (weight key) framesPositive
  have headSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
      (before ++ rest.reverse) ++ (rebuild weight subtree, weight key + HeavyPath.mass weight subtree) :: after := by
    simpa only [head, List.reverse_cons, List.append_assoc, List.singleton_append] using split
  obtain ⟨depth, slot⟩ := locate_split headSplit
  have charged : weight key ≤ weight key + HeavyPath.mass weight subtree := by
    have mass := HeavyPath.mass_nonnegative (positive_nonnegative positive)
    linarith
  have existsKey := fringe_successor headSplit nonempty
  rw [combined_tree] at existsKey
  have bound := separator_estimate keyPositive charged (located_mass valid slot).2 sourceMass
    (located_successor_bound valid slot (lt_of_lt_of_le keyPositive charged) existsKey)
  have index : fringeSpan (before ++ rest.reverse) + (rebuild weight subtree).size =
      fringeSpan before + fringeSpan (sideSlots weight (rebuild weight) boundary (weight key) fs) - 1 := by
    rw [fringeSpan_append, fringeSpan_reverse, head]
    change fringeSpan before + fringeSpan rest + (rebuild weight subtree).size =
      fringeSpan before + ((rebuild weight subtree).size + 1 + fringeSpan rest) - 1
    omega
  simpa only [index] using bound

end RotationBST.HeavyPath.Finger
