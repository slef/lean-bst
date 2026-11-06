module

public import RotationBST.Structures.HeavyPath.Finger.History.DepthStep
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree Recursive.History

theorem sideSlots_head {α : Type} {weight : α → ℝ} {boundary : LabelledTree α} {shape : Tree}
    (boundaryPositive : Positive weight boundary) (carry : ℝ) {fs : List (Entry α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f.source) ∧ 0 < weight (frameKey f.source)) :
    ∃ subtree payloadShape rest, Positive weight subtree ∧
      sideSlots weight boundary shape carry fs =
        (payloadShape, carry + HeavyPath.mass weight subtree) :: rest := by
  cases fs with
  | nil => exact ⟨boundary, shape, [], boundaryPositive, rfl⟩
  | cons f fs => exact ⟨framePayload f.source, f.shape, _, (framesPositive f (by simp)).1, rfl⟩

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
    {whole : ℝ} (sourceMass : p.mass ≤ whole) {boundary : LabelledTree α} {shape : Tree}
    (boundaryPositive : Positive weight boundary) {key : α} (keyPositive : 0 < weight key)
    {fs : List (Entry α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f.source) ∧ 0 < weight (frameKey f.source))
    {before after : List (Tree × ℝ)}
    (split : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
      before ++ sideSlots weight boundary shape (weight key) fs ++ after)
    (existsKey : 0 < fringeSpan before) :
    (Tree.depth p.tree (fringeSpan before - 1) : ℝ) ≤
      15 + 15 * Real.logb 2 (whole / weight key) := by
  obtain ⟨subtree, payloadShape, rest, positive, head⟩ := sideSlots_head (shape := shape) boundaryPositive (weight key) framesPositive
  have headSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
      before ++ (payloadShape, weight key + HeavyPath.mass weight subtree) :: (rest ++ after) := by
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
    {whole : ℝ} (sourceMass : p.mass ≤ whole) {boundary : LabelledTree α} {shape : Tree}
    (boundaryPositive : Positive weight boundary) {key : α} (keyPositive : 0 < weight key)
    {fs : List (Entry α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f.source) ∧ 0 < weight (frameKey f.source))
    {before after : List (Tree × ℝ)}
    (split : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
      before ++ (sideSlots weight boundary shape (weight key) fs).reverse ++ after)
    (nonempty : after ≠ []) :
    (Tree.depth p.tree
      (fringeSpan before + fringeSpan (sideSlots weight boundary shape (weight key) fs) - 1) : ℝ) ≤
      15 + 15 * Real.logb 2 (whole / weight key) := by
  obtain ⟨subtree, payloadShape, rest, positive, head⟩ := sideSlots_head (shape := shape) boundaryPositive (weight key) framesPositive
  have headSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
      (before ++ rest.reverse) ++ (payloadShape, weight key + HeavyPath.mass weight subtree) :: after := by
    simpa only [head, List.reverse_cons, List.append_assoc, List.singleton_append] using split
  obtain ⟨depth, slot⟩ := locate_split headSplit
  have charged : weight key ≤ weight key + HeavyPath.mass weight subtree := by
    have mass := HeavyPath.mass_nonnegative (positive_nonnegative positive)
    linarith
  have existsKey := fringe_successor headSplit nonempty
  rw [combined_tree] at existsKey
  have bound := separator_estimate keyPositive charged (located_mass valid slot).2 sourceMass
    (located_successor_bound valid slot (lt_of_lt_of_le keyPositive charged) existsKey)
  have index : fringeSpan (before ++ rest.reverse) + payloadShape.size =
      fringeSpan before + fringeSpan (sideSlots weight boundary shape (weight key) fs) - 1 := by
    rw [fringeSpan_append, fringeSpan_reverse, head]
    change fringeSpan before + fringeSpan rest + payloadShape.size =
      fringeSpan before + (payloadShape.size + 1 + fringeSpan rest) - 1
    omega
  simpa only [index] using bound

end RotationBST.HeavyPath.Finger.History
