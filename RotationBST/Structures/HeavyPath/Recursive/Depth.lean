module

public import RotationBST.Structures.HeavyPath.Recursive.Inorder
public import RotationBST.Models.Pointer.Search
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive
open Paired LabelledCursor PopTart PopTart.WeightedTree

private theorem payload_ranks {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil)
    {frame : Frame α} (member : frame ∈ (extract weight t).context)
    (child : RanksSatisfy (fun rank key =>
      (Tree.depth (rebuild weight (framePayload frame)) rank : ℝ) ≤
        7 + 15 * Real.logb 2 (HeavyPath.mass weight (framePayload frame) / weight key))
      0 (framePayload frame).inorder)
    {offset depth : Nat}
    (slot : LocatedSlot (.node (rootPair weight t).lower.decode (rootPair weight t).upper.decode.mirror)
      (rebuild weight (framePayload frame)) (frameMass weight frame) offset depth) :
    RanksSatisfy (fun rank key => (Tree.depth (rebuild weight t) rank : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight key)) offset (framePayload frame).inorder := by
  intro before key after split
  have childPositive := extract_payload_positive positive member
  have keyMember : key ∈ (framePayload frame).inorder := by rw [split]; simp
  obtain ⟨keyPositive, keyMass⟩ := inorder_weight childPositive keyMember
  have inside : before.length < (rebuild weight (framePayload frame)).size := by
    rw [rebuild_size childPositive, ← Representation.Bridge.inorder_length, split]
    simp only [List.length_append, List.length_cons]
    omega
  exact payload_depth_step positive nonempty member slot inside keyPositive keyMass
    (by simpa only [Nat.zero_add] using child before key after split)

/-- Exhaustively account for endpoint, separator, and payload occurrences.
The only recursive premise concerns strictly smaller off-path source trees. -/
theorem depth_from_children {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil)
    (children : ∀ frame ∈ (extract weight t).context,
      RanksSatisfy (fun rank key => (Tree.depth (rebuild weight (framePayload frame)) rank : ℝ) ≤
        7 + 15 * Real.logb 2 (HeavyPath.mass weight (framePayload frame) / weight key))
        0 (framePayload frame).inorder) :
    RanksSatisfy (fun rank key => (Tree.depth (rebuild weight t) rank : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight key)) 0 t.inorder := by
  let p := rootPair weight t
  let cs := (extract weight t).context
  let P := fun rank key => (Tree.depth (rebuild weight t) rank : ℝ) ≤
    7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight key)
  obtain ⟨endpoint, focus, tree, valid, partition, lowerFringe, upperFringe⟩ := rebuild_pair positive nonempty
  change rebuild weight t = p.tree at tree
  change p.lower.decode.fringe = _ at lowerFringe
  change p.upper.decode.mirror.fringe = _ at upperFringe
  rw [← lowerFrames_slots] at lowerFringe
  rw [← upperFrames_slots] at upperFringe
  have inorder : t.inorder = (lowerFrames cs).flatMap lowerBlock ++
      [endpoint] ++ (upperFrames cs).flatMap upperBlock := by
    have h := context_inorder cs (extract weight t).focus
    change (extract weight t).tree.inorder = _ at h
    rw [HeavyPath.Results.extract_tree, focus] at h
    simpa only [LabelledTree.inorder, List.nil_append] using h
  have lowerSizes : ∀ f ∈ lowerFrames cs,
      (lowerBlock f).length = (rebuild weight (framePayload f)).size + 1 := by
    intro f hf
    rw [(block_length f).1, rebuild_size (extract_payload_positive positive (lowerFrames_mem hf))]
  have upperSizes : ∀ f ∈ upperFrames cs,
      (upperBlock f).length = (rebuild weight (framePayload f)).size + 1 := by
    intro f hf
    rw [(block_length f).2, rebuild_size (extract_payload_positive positive (upperFrames_mem hf))]
  have lowerLength : ((lowerFrames cs).flatMap lowerBlock).length = p.lower.decode.tree.size := by
    have span := fringeSpan_fringe p.lower.decode
    rw [lowerFringe, fringeSpan_append,
      fringe_blocks_span weight (rebuild weight) lowerBlock (lowerFrames cs) lowerSizes] at span
    simp only [fringeSpan, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Tree.size, Nat.zero_add, Nat.add_zero] at span
    omega
  have lowerBound : RanksSatisfy P 0 ((lowerFrames cs).flatMap lowerBlock) := by
    refine fringe_blocks_ranks weight (rebuild weight) lowerBlock P 0 (lowerFrames cs) lowerSizes ?_
      (whole := p.lower.decode) (before := []) (after := [(.nil, 0)]) ?_ ?_
    · intro f hf offset depth slot base same
      have member : f ∈ (extract weight t).context := lowerFrames_mem hf
      have combined : LocatedSlot (.node p.lower.decode p.upper.decode.mirror)
          (rebuild weight (framePayload f)) (frameMass weight f) offset (depth + 1) := .left slot
      have off : offset = base := by omega
      subst offset
      change RanksSatisfy P base ((framePayload f).inorder ++ [frameKey f])
      apply RanksSatisfy.append (payload_ranks positive nonempty member (children f member) combined)
      apply RanksSatisfy.singleton
      have fits := slot.fits
      have existsKey : base + (rebuild weight (framePayload f)).size < (rebuild weight t).size := by
        rw [tree]
        change _ < p.lower.decode.tree.size + 1 + p.upper.decode.tree.mirror.size
        omega
      have bound := successor_depth_step positive nonempty member combined existsKey
      simpa only [Representation.Bridge.inorder_length,
        rebuild_size (extract_payload_positive positive member)] using bound
    · simpa only [List.nil_append] using lowerFringe
    · rfl
  have endpointBound : P p.lower.decode.tree.size endpoint := by
    have member : endpoint ∈ t.inorder := by rw [inorder]; simp
    obtain ⟨keyPositive, keyMass⟩ := inorder_weight positive member
    have logarithm : 0 ≤ Real.logb 2 (HeavyPath.mass weight t / weight endpoint) := by
      apply Real.logb_nonneg (by norm_num)
      exact (le_div_iff₀ keyPositive).mpr (by simpa only [one_mul] using keyMass)
    dsimp only [P]
    rw [tree]
    have depthZero : Tree.depth p.tree p.lower.decode.tree.size = 0 := by
      simp [Stacks.tree, Tree.depth]
    rw [depthZero]
    norm_num only [Nat.cast_zero]
    linarith
  have upperBound : RanksSatisfy P (p.lower.decode.tree.size + 1)
      ((upperFrames cs).flatMap upperBlock) := by
    refine fringe_blocks_ranks weight (rebuild weight) upperBlock P 1 (upperFrames cs) upperSizes ?_
      (whole := .node p.lower.decode p.upper.decode.mirror)
      (before := p.lower.decode.fringe ++ [(.nil, 0)]) (after := []) ?_ ?_
    · intro f hf offset depth slot base same
      have member : f ∈ (extract weight t).context := upperFrames_mem hf
      change RanksSatisfy P base ([frameKey f] ++ (framePayload f).inorder)
      apply RanksSatisfy.append
      · apply RanksSatisfy.singleton
        have bound := predecessor_depth_step positive nonempty member slot (by omega)
        simpa only [same, Nat.add_sub_cancel] using bound
      · simpa only [List.length_singleton, ← same] using
          payload_ranks positive nonempty member (children f member) slot
    · simp only [WeightedTree.fringe, upperFringe, List.append_assoc, List.append_nil, cs]
    · rw [fringeSpan_append, fringeSpan_fringe]
      rfl
  change RanksSatisfy P 0 t.inorder
  rw [inorder, List.append_assoc]
  apply RanksSatisfy.append lowerBound
  apply RanksSatisfy.append
  · apply RanksSatisfy.singleton
    simpa only [Nat.zero_add, lowerLength] using endpointBound
  · simpa only [Nat.zero_add, lowerLength, List.length_singleton] using upperBound

/-- Every original key occurrence has logarithmic weighted depth in the
canonical recursive representation. The theorem needs no ordering or distinctness
assumption; `before.length` identifies the occurrence's original inorder rank. -/
theorem rebuild_depth {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {before after : List α} {key : α}
    (occurrence : t.inorder = before ++ key :: after) :
    (Tree.depth (rebuild weight t) before.length : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight key) := by
  have all : ∀ n (s : LabelledTree α), s.erase.size = n → Positive weight s →
      RanksSatisfy (fun rank x => (Tree.depth (rebuild weight s) rank : ℝ) ≤
        7 + 15 * Real.logb 2 (HeavyPath.mass weight s / weight x)) 0 s.inorder := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro s size pos
      by_cases empty : s = .nil
      · subst s
        exact RanksSatisfy.nil _ _
      · apply depth_from_children pos empty
        intro frame member
        apply ih (framePayload frame).erase.size
        · rw [← size]
          exact extract_payload_size weight s member
        · rfl
        · exact extract_payload_positive pos member
  simpa only [Nat.zero_add] using all t.erase.size t rfl positive before key after occurrence

theorem rebuild_depth_at {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (rank : Fin t.inorder.length) :
    (Tree.depth (rebuild weight t) rank.val : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight (t.inorder[rank.val]'rank.isLt)) := by
  have split : t.inorder = t.inorder.take rank.val ++
      t.inorder[rank.val] :: t.inorder.drop (rank.val + 1) := by
    rw [← List.drop_eq_getElem_cons rank.isLt, List.take_append_drop]
  have bound := rebuild_depth positive split
  simpa only [List.length_take, Nat.min_eq_left rank.isLt.le] using bound

theorem rebuild_unit_depth {α : Type} (t : LabelledTree α) (rank : Nat)
    (valid : rank < t.erase.size) :
    (Tree.depth (rebuild (fun _ => 1) t) rank : ℝ) ≤
      7 + 15 * Real.logb 2 (t.erase.size : ℝ) := by
  have inside : rank < t.inorder.length := by simpa only [Representation.Bridge.inorder_length] using valid
  simpa only [unit_mass, div_one] using rebuild_depth_at (unit_positive t) ⟨rank, inside⟩

/-- A real visit and return in the initialized representation, with the
request charge and both walks counted. This does not simulate a source update. -/
theorem rebuild_search_walk {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (rank : Fin t.inorder.length) :
    ∃ (visited : Pointer.Config) (cost : Nat),
      visited.tree = rebuild weight t ∧ visited.key? = some rank.val ∧
      Pointer.Trace ⟨rebuild weight t, []⟩ visited cost ∧
      Pointer.Trace visited ⟨rebuild weight t, []⟩ cost ∧
      (1 + 2 * cost : ℝ) ≤
        15 + 30 * Real.logb 2 (HeavyPath.mass weight t / weight (t.inorder[rank.val]'rank.isLt)) := by
  have inside : rank.val < (rebuild weight t).size := by
    rw [rebuild_size positive, ← Representation.Bridge.inorder_length]
    exact rank.isLt
  obtain ⟨visited, tree, key, outward, inward⟩ := Pointer.search_walk (rebuild weight t) rank.val inside
  refine ⟨visited, Tree.depth (rebuild weight t) rank.val, tree, key, outward, inward, ?_⟩
  have bound := rebuild_depth_at positive rank
  linarith

end RotationBST.HeavyPath.Recursive
