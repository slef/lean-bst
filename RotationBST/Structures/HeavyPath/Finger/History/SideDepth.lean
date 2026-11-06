module

public import RotationBST.Structures.HeavyPath.Finger.History.Occurrences
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree Recursive.History

theorem lower_ranks {α : Type} {weight : α → ℝ} {p : Pair} (valid : p.Valid)
    {whole : ℝ} (sourceMass : p.mass ≤ whole) {boundary : LabelledTree α}
    {shape : Tree} {credit : Nat} (boundaryLayout : Recursive.History.Layout weight boundary shape credit) {carry : ℝ} (carryNonnegative : 0 ≤ carry)
    {fs : List (Entry α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f.source) ∧ 0 < weight (frameKey f.source))
    (children : ∀ e ∈ fs, Recursive.History.Layout weight (framePayload e.source) e.shape e.credit)
    {before after : List (Tree × ℝ)}
    (split : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
      before ++ sideSlots weight boundary shape carry fs ++ after) :
    RanksSatisfy (fun rank key => (Tree.depth p.tree rank : ℝ) ≤
      15 + 15 * Real.logb 2 (whole / weight key)) (fringeSpan before)
      (fs.flatMap Entry.lowerBlock ++ boundary.inorder) := by
  have boundaryPositive := layout_positive boundaryLayout
  let P := fun rank key => (Tree.depth p.tree rank : ℝ) ≤
    15 + 15 * Real.logb 2 (whole / weight key)
  induction fs generalizing before after carry with
  | nil =>
    have headSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
        before ++ (shape, carry + HeavyPath.mass weight boundary) :: after := by
      simpa only [sideSlots, List.singleton_append, List.append_assoc] using split
    obtain ⟨depth, slot⟩ := locate_split headSplit
    exact payload_ranks valid sourceMass boundaryLayout (by linarith) slot
  | cons f fs ih =>
    have first := framesPositive f (by simp)
    have child := children f (by simp)
    have laterChildren : ∀ e ∈ fs, Recursive.History.Layout weight (framePayload e.source) e.shape e.credit :=
      fun e he => children e (by simp [he])
    have later : ∀ g ∈ fs, Positive weight (framePayload g.source) ∧ 0 < weight (frameKey g.source) :=
      fun g hg => framesPositive g (by simp [hg])
    let entry := (f.shape, carry + HeavyPath.mass weight (framePayload f.source))
    have headSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
        before ++ entry :: (sideSlots weight boundary shape (weight (frameKey f.source)) fs ++ after) := by
      simpa only [sideSlots, List.append_assoc, List.cons_append] using split
    obtain ⟨depth, slot⟩ := locate_split headSplit
    have payload := payload_ranks valid sourceMass child (by linarith) slot
    have tailSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
        (before ++ [entry]) ++ sideSlots weight boundary shape (weight (frameKey f.source)) fs ++ after := by
      simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using headSplit
    have newSpan : fringeSpan (before ++ [entry]) = fringeSpan before + (framePayload f.source).inorder.length + 1 := by
      rw [fringeSpan_append]
      change fringeSpan before + (f.shape.size + 1 + 0) = _
      rw [layout_size child, Representation.Bridge.inorder_length]
      omega
    have separator := side_predecessor_bound valid sourceMass boundaryPositive first.2 later tailSplit
      (by rw [newSpan]; omega)
    have tail := ih first.2.le later laterChildren tailSplit
    change RanksSatisfy P (fringeSpan before) _
    simp only [List.flatMap_cons, Entry.lowerBlock, lowerBlock, List.append_assoc]
    apply RanksSatisfy.append payload
    apply RanksSatisfy.append
    · apply RanksSatisfy.singleton
      simpa only [newSpan, Nat.add_sub_cancel] using separator
    · simpa only [newSpan, List.length_singleton] using tail

theorem upper_ranks {α : Type} {weight : α → ℝ} {p : Pair} (valid : p.Valid)
    {whole : ℝ} (sourceMass : p.mass ≤ whole) {boundary : LabelledTree α}
    {shape : Tree} {credit : Nat} (boundaryLayout : Recursive.History.Layout weight boundary shape credit) {carry : ℝ} (carryNonnegative : 0 ≤ carry)
    {fs : List (Entry α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f.source) ∧ 0 < weight (frameKey f.source))
    (children : ∀ e ∈ fs, Recursive.History.Layout weight (framePayload e.source) e.shape e.credit)
    {before after : List (Tree × ℝ)}
    (split : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
      before ++ (sideSlots weight boundary shape carry fs).reverse ++ after) :
    RanksSatisfy (fun rank key => (Tree.depth p.tree rank : ℝ) ≤
      15 + 15 * Real.logb 2 (whole / weight key)) (fringeSpan before)
      (boundary.inorder ++ fs.reverse.flatMap Entry.upperBlock) := by
  have boundaryPositive := layout_positive boundaryLayout
  let P := fun rank key => (Tree.depth p.tree rank : ℝ) ≤
    15 + 15 * Real.logb 2 (whole / weight key)
  induction fs generalizing before after carry with
  | nil =>
    have headSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
        before ++ (shape, carry + HeavyPath.mass weight boundary) :: after := by
      simpa only [sideSlots, List.reverse_singleton, List.singleton_append, List.append_assoc] using split
    obtain ⟨depth, slot⟩ := locate_split headSplit
    simpa only [List.reverse_nil, List.flatMap_nil, List.append_nil] using
      payload_ranks valid sourceMass boundaryLayout (by linarith) slot
  | cons f fs ih =>
    have first := framesPositive f (by simp)
    have child := children f (by simp)
    have laterChildren : ∀ e ∈ fs, Recursive.History.Layout weight (framePayload e.source) e.shape e.credit :=
      fun e he => children e (by simp [he])
    have later : ∀ g ∈ fs, Positive weight (framePayload g.source) ∧ 0 < weight (frameKey g.source) :=
      fun g hg => framesPositive g (by simp [hg])
    let entry := (f.shape, carry + HeavyPath.mass weight (framePayload f.source))
    let tailSlots := sideSlots weight boundary shape (weight (frameKey f.source)) fs
    let keys := boundary.inorder ++ fs.reverse.flatMap Entry.upperBlock
    have tailSpan : fringeSpan tailSlots = keys.length + 1 :=
      (sideSlots_lengths boundaryLayout (weight (frameKey f.source)) laterChildren).2
    have headSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
        (before ++ tailSlots.reverse) ++ entry :: after := by
      simpa only [sideSlots, List.reverse_cons, List.append_assoc, List.singleton_append] using split
    obtain ⟨depth, slot⟩ := locate_split headSplit
    have payload : RanksSatisfy P (fringeSpan before + keys.length + 1) (framePayload f.source).inorder := by
      have found := payload_ranks valid sourceMass child (by linarith) slot
      simpa only [fringeSpan_append, fringeSpan_reverse, tailSpan, Nat.add_assoc] using found
    have tailSplit : (WeightedTree.node p.lower.decode.mirror p.upper.decode).fringe =
        before ++ tailSlots.reverse ++ (entry :: after) := headSplit
    have tail : RanksSatisfy P (fringeSpan before) keys := ih first.2.le later laterChildren tailSplit
    have separator : P (fringeSpan before + keys.length) (frameKey f.source) := by
      have bound := side_successor_bound valid sourceMass boundaryPositive first.2 later tailSplit (by simp)
      change (Tree.depth p.tree (fringeSpan before + fringeSpan tailSlots - 1) : ℝ) ≤ _ at bound
      simpa only [tailSpan, ← Nat.add_assoc, Nat.add_sub_cancel] using bound
    have ending : RanksSatisfy P (fringeSpan before + keys.length) ([frameKey f.source] ++ (framePayload f.source).inorder) :=
      RanksSatisfy.append (RanksSatisfy.singleton separator) payload
    have joined := RanksSatisfy.append tail ending
    simpa only [keys, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, Entry.upperBlock, upperBlock, List.singleton_append, List.append_assoc] using joined

end RotationBST.HeavyPath.Finger.History
