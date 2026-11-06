module

public import RotationBST.Structures.HeavyPath.Finger.Occurrences
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree

theorem lower_ranks {α : Type} {weight : α → ℝ} {p : Pair} (valid : p.Valid)
    {whole : ℝ} (sourceMass : p.mass ≤ whole) {boundary : LabelledTree α}
    (boundaryPositive : Positive weight boundary) {carry : ℝ} (carryNonnegative : 0 ≤ carry)
    {fs : List (Frame α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f) ∧ 0 < weight (frameKey f))
    {before after : List (Tree × ℝ)}
    (split : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
      before ++ sideSlots weight (rebuild weight) boundary carry fs ++ after) :
    RanksSatisfy (fun rank key => (Tree.depth p.tree rank : ℝ) ≤
      15 + 15 * Real.logb 2 (whole / weight key)) (fringeSpan before)
      (fs.flatMap lowerBlock ++ boundary.inorder) := by
  let P := fun rank key => (Tree.depth p.tree rank : ℝ) ≤
    15 + 15 * Real.logb 2 (whole / weight key)
  induction fs generalizing before after carry with
  | nil =>
    have headSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
        before ++ (rebuild weight boundary, carry + HeavyPath.mass weight boundary) :: after := by
      simpa only [sideSlots, List.singleton_append, List.append_assoc] using split
    obtain ⟨depth, slot⟩ := locate_split headSplit
    exact payload_ranks valid sourceMass boundaryPositive (by linarith) slot
  | cons f fs ih =>
    have first := framesPositive f (by simp)
    have later : ∀ g ∈ fs, Positive weight (framePayload g) ∧ 0 < weight (frameKey g) :=
      fun g hg => framesPositive g (by simp [hg])
    let entry := (rebuild weight (framePayload f), carry + HeavyPath.mass weight (framePayload f))
    have headSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
        before ++ entry :: (sideSlots weight (rebuild weight) boundary (weight (frameKey f)) fs ++ after) := by
      simpa only [sideSlots, List.append_assoc, List.cons_append] using split
    obtain ⟨depth, slot⟩ := locate_split headSplit
    have payload := payload_ranks valid sourceMass first.1 (by linarith) slot
    have tailSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
        (before ++ [entry]) ++ sideSlots weight (rebuild weight) boundary (weight (frameKey f)) fs ++ after := by
      simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using headSplit
    have newSpan : fringeSpan (before ++ [entry]) = fringeSpan before + (framePayload f).inorder.length + 1 := by
      rw [fringeSpan_append]
      change fringeSpan before + ((rebuild weight (framePayload f)).size + 1 + 0) = _
      rw [rebuild_size first.1, Representation.Bridge.inorder_length]
      omega
    have separator := side_predecessor_bound valid sourceMass boundaryPositive first.2 later tailSplit
      (by rw [newSpan]; omega)
    have tail := ih first.2.le later tailSplit
    change RanksSatisfy P (fringeSpan before) _
    simp only [List.flatMap_cons, lowerBlock, List.append_assoc]
    apply RanksSatisfy.append payload
    apply RanksSatisfy.append
    · apply RanksSatisfy.singleton
      simpa only [newSpan, Nat.add_sub_cancel] using separator
    · simpa only [newSpan, List.length_singleton] using tail

theorem upper_ranks {α : Type} {weight : α → ℝ} {p : Pair} (valid : p.Valid)
    {whole : ℝ} (sourceMass : p.mass ≤ whole) {boundary : LabelledTree α}
    (boundaryPositive : Positive weight boundary) {carry : ℝ} (carryNonnegative : 0 ≤ carry)
    {fs : List (Frame α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f) ∧ 0 < weight (frameKey f))
    {before after : List (Tree × ℝ)}
    (split : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
      before ++ (sideSlots weight (rebuild weight) boundary carry fs).reverse ++ after) :
    RanksSatisfy (fun rank key => (Tree.depth p.tree rank : ℝ) ≤
      15 + 15 * Real.logb 2 (whole / weight key)) (fringeSpan before)
      (boundary.inorder ++ fs.reverse.flatMap upperBlock) := by
  let P := fun rank key => (Tree.depth p.tree rank : ℝ) ≤
    15 + 15 * Real.logb 2 (whole / weight key)
  induction fs generalizing before after carry with
  | nil =>
    have headSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
        before ++ (rebuild weight boundary, carry + HeavyPath.mass weight boundary) :: after := by
      simpa only [sideSlots, List.reverse_singleton, List.singleton_append, List.append_assoc] using split
    obtain ⟨depth, slot⟩ := locate_split headSplit
    simpa only [List.reverse_nil, List.flatMap_nil, List.append_nil] using
      payload_ranks valid sourceMass boundaryPositive (by linarith) slot
  | cons f fs ih =>
    have first := framesPositive f (by simp)
    have later : ∀ g ∈ fs, Positive weight (framePayload g) ∧ 0 < weight (frameKey g) :=
      fun g hg => framesPositive g (by simp [hg])
    let entry := (rebuild weight (framePayload f), carry + HeavyPath.mass weight (framePayload f))
    let tailSlots := sideSlots weight (rebuild weight) boundary (weight (frameKey f)) fs
    let keys := boundary.inorder ++ fs.reverse.flatMap upperBlock
    have tailSpan : fringeSpan tailSlots = keys.length + 1 :=
      (sideSlots_lengths boundaryPositive (weight (frameKey f)) later).2
    have headSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
        (before ++ tailSlots.reverse) ++ entry :: after := by
      simpa only [sideSlots, List.reverse_cons, List.append_assoc, List.singleton_append] using split
    obtain ⟨depth, slot⟩ := locate_split headSplit
    have payload : RanksSatisfy P (fringeSpan before + keys.length + 1) (framePayload f).inorder := by
      have found := payload_ranks valid sourceMass first.1 (by linarith) slot
      simpa only [fringeSpan_append, fringeSpan_reverse, tailSpan, Nat.add_assoc] using found
    have tailSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
        before ++ tailSlots.reverse ++ (entry :: after) := headSplit
    have tail : RanksSatisfy P (fringeSpan before) keys := ih first.2.le later tailSplit
    have separator : P (fringeSpan before + keys.length) (frameKey f) := by
      have bound := side_successor_bound valid sourceMass boundaryPositive first.2 later tailSplit (by simp)
      change (Tree.depth p.tree (fringeSpan before + fringeSpan tailSlots - 1) : ℝ) ≤ _ at bound
      simpa only [tailSpan, ← Nat.add_assoc, Nat.add_sub_cancel] using bound
    have ending : RanksSatisfy P (fringeSpan before + keys.length) ([frameKey f] ++ (framePayload f).inorder) :=
      RanksSatisfy.append (RanksSatisfy.singleton separator) payload
    have joined := RanksSatisfy.append tail ending
    simpa only [keys, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, upperBlock, List.singleton_append, List.append_assoc] using joined

end RotationBST.HeavyPath.Finger
