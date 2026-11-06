module

public import RotationBST.Structures.HeavyPath.Recursive.History.DepthStep
public import RotationBST.Models.Pointer.Search
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History
open Paired LabelledCursor PopTart PopTart.WeightedTree

private theorem payload_ranks {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {p : Stacks} (valid : p.Valid) (sourceMass : p.mass ≤ mass weight t)
    {e : Entry α} (member : e.source ∈ (extract weight t).context)
    (size : e.shape.size = (framePayload e.source).erase.size)
    (child : RanksSatisfy (fun rank key => (Tree.depth e.shape rank : ℝ) ≤
      7 + 15 * Real.logb 2 (mass weight (framePayload e.source) / weight key))
      0 (framePayload e.source).inorder)
    {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror)
      e.shape (frameMass weight e.source) offset depth) :
    RanksSatisfy (fun rank key => (Tree.depth p.tree rank : ℝ) ≤
      7 + 15 * Real.logb 2 (mass weight t / weight key)) offset (framePayload e.source).inorder := by
  intro before key after split
  have childPositive := extract_payload_positive positive member
  have keyMember : key ∈ (framePayload e.source).inorder := by rw [split]; simp
  obtain ⟨keyPositive, keyMass⟩ := inorder_weight childPositive keyMember
  have inside : before.length < e.shape.size := by
    rw [size, ← Representation.Bridge.inorder_length, split]
    simp only [List.length_append, List.length_cons]
    omega
  exact payload_depth_step positive valid sourceMass member slot inside keyPositive keyMass
    (by simpa only [Nat.zero_add] using child before key after split)

/-- The proof enumerates every occurrence using the actual fringes. It needs
no relation to a canonical sequence of stack repairs. -/
theorem path_depth {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    {es : List (Entry α)} {p : Stacks} (positive : Positive weight t) (nonempty : t ≠ .nil)
    (context : es.map Entry.source = (extract weight t).context) (valid : PathValid weight es p)
    (sizes : ∀ e ∈ es, e.shape.size = (framePayload e.source).erase.size)
    (children : ∀ e ∈ es, RanksSatisfy (fun rank key => (Tree.depth e.shape rank : ℝ) ≤
      7 + 15 * Real.logb 2 (mass weight (framePayload e.source) / weight key))
      0 (framePayload e.source).inorder) :
    RanksSatisfy (fun rank key => (Tree.depth p.tree rank : ℝ) ≤
      7 + 15 * Real.logb 2 (mass weight t / weight key)) 0 t.inorder := by
  let P := fun rank key => (Tree.depth p.tree rank : ℝ) ≤
    7 + 15 * Real.logb 2 (mass weight t / weight key)
  have sourceMass := path_mass_le positive nonempty context valid
  obtain ⟨endpoint, focus⟩ := HeavyPath.Results.extract_terminal positive nonempty
  have inorder := entries_inorder context focus
  have lowerSizes : ∀ e ∈ lower es, (Entry.lowerBlock e).length = e.shape.size + 1 := by
    intro e member
    rw [Entry.lowerBlock, (block_length e.source).1, sizes e (lower_mem member)]
  have upperSizes : ∀ e ∈ upper es, (Entry.upperBlock e).length = e.shape.size + 1 := by
    intro e member
    rw [Entry.upperBlock, (block_length e.source).2, sizes e (upper_mem member)]
  have lowerLength : ((lower es).flatMap Entry.lowerBlock).length = p.lower.decode.tree.size := by
    have span := fringeSpan_fringe p.lower.decode
    rw [valid.lower, fringeSpan_append, blocks_span weight Entry.lowerBlock (lower es) lowerSizes] at span
    simp only [fringeSpan, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Tree.size, Nat.zero_add, Nat.add_zero] at span
    omega
  have lowerBound : RanksSatisfy P 0 ((lower es).flatMap Entry.lowerBlock) := by
    refine blocks_ranks weight Entry.lowerBlock P 0 (lower es) lowerSizes ?_
      (whole := p.lower.decode) (before := []) (after := [(.nil, 0)]) ?_ ?_
    · intro e member offset depth slot base same
      have original := lower_mem member
      have sourceMember := source_member context original
      have combined : LocatedSlot (.node p.lower.decode p.upper.decode.mirror)
          e.shape (frameMass weight e.source) offset (depth + 1) := .left slot
      have off : offset = base := by omega
      subst offset
      change RanksSatisfy P base ((framePayload e.source).inorder ++ [frameKey e.source])
      apply RanksSatisfy.append (payload_ranks positive valid.pair sourceMass sourceMember
        (sizes e original) (children e original) combined)
      apply RanksSatisfy.singleton
      have fits := slot.fits
      have existsKey : base + e.shape.size < p.tree.size := by
        change _ < p.lower.decode.tree.size + 1 + p.upper.decode.tree.mirror.size
        omega
      have bound := successor_depth_step positive valid.pair sourceMass sourceMember combined existsKey
      simpa only [Representation.Bridge.inorder_length, sizes e original] using bound
    · simpa only [List.nil_append] using valid.lower
    · rfl
  have endpointBound : P p.lower.decode.tree.size endpoint := by
    have member : endpoint ∈ t.inorder := by rw [inorder]; simp
    obtain ⟨keyPositive, keyMass⟩ := inorder_weight positive member
    have logarithm : 0 ≤ Real.logb 2 (mass weight t / weight endpoint) := by
      apply Real.logb_nonneg (by norm_num)
      exact (le_div_iff₀ keyPositive).mpr (by simpa only [one_mul] using keyMass)
    dsimp only [P]
    have depthZero : Tree.depth p.tree p.lower.decode.tree.size = 0 := by
      simp [Stacks.tree, Tree.depth]
    rw [depthZero]
    norm_num only [Nat.cast_zero]
    linarith
  have upperBound : RanksSatisfy P (p.lower.decode.tree.size + 1) ((upper es).flatMap Entry.upperBlock) := by
    refine blocks_ranks weight Entry.upperBlock P 1 (upper es) upperSizes ?_
      (whole := .node p.lower.decode p.upper.decode.mirror)
      (before := p.lower.decode.fringe ++ [(.nil, 0)]) (after := []) ?_ ?_
    · intro e member offset depth slot base same
      have original := upper_mem member
      have sourceMember := source_member context original
      change RanksSatisfy P base ([frameKey e.source] ++ (framePayload e.source).inorder)
      apply RanksSatisfy.append
      · apply RanksSatisfy.singleton
        have bound := predecessor_depth_step positive valid.pair sourceMass sourceMember slot (by omega)
        simpa only [same, Nat.add_sub_cancel] using bound
      · simpa only [List.length_singleton, ← same] using
          payload_ranks positive valid.pair sourceMass sourceMember (sizes e original) (children e original) slot
    · simp only [WeightedTree.fringe, valid.upper, List.append_assoc, List.append_nil]
    · rw [fringeSpan_append, fringeSpan_fringe]
      rfl
  change RanksSatisfy P 0 t.inorder
  rw [inorder, List.append_assoc]
  apply RanksSatisfy.append lowerBound
  apply RanksSatisfy.append
  · apply RanksSatisfy.singleton
    simpa only [Nat.zero_add, lowerLength] using endpointBound
  · simpa only [Nat.zero_add, lowerLength, List.length_singleton] using upperBound

/-- Recursive validity alone implies the global weighted depth bound. In
particular, height is not an assumed field of the history invariant. -/
theorem layout_ranks {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree} {credit : Nat}
    (layout : Layout weight t shape credit) :
    RanksSatisfy (fun rank key => (Tree.depth shape rank : ℝ) ≤
      7 + 15 * Real.logb 2 (mass weight t / weight key)) 0 t.inorder := by
  induction layout with
  | nil => exact RanksSatisfy.nil _ _
  | path positive nonempty context valid children ih =>
    exact path_depth positive nonempty context valid (fun e member => layout_size (children e member)) ih

theorem layout_depth {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree} {credit : Nat}
    (layout : Layout weight t shape credit) {before after : List α} {key : α}
    (occurrence : t.inorder = before ++ key :: after) :
    (Tree.depth shape before.length : ℝ) ≤ 7 + 15 * Real.logb 2 (mass weight t / weight key) := by
  simpa only [Nat.zero_add] using layout_ranks layout before key after occurrence

theorem layout_depth_at {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree} {credit : Nat}
    (layout : Layout weight t shape credit) (rank : Fin t.inorder.length) :
    (Tree.depth shape rank.val : ℝ) ≤
      7 + 15 * Real.logb 2 (mass weight t / weight (t.inorder[rank.val]'rank.isLt)) := by
  have split : t.inorder = t.inorder.take rank.val ++ t.inorder[rank.val] :: t.inorder.drop (rank.val + 1) := by
    rw [← List.drop_eq_getElem_cons rank.isLt, List.take_append_drop]
  have bound := layout_depth layout split
  simpa only [List.length_take, Nat.min_eq_left rank.isLt.le] using bound

theorem layout_search_walk {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree} {credit : Nat}
    (layout : Layout weight t shape credit) (rank : Fin t.inorder.length) :
    ∃ (visited : Pointer.Config) (cost : Nat), visited.tree = shape ∧ visited.key? = some rank.val ∧
      Pointer.Trace ⟨shape, []⟩ visited cost ∧ Pointer.Trace visited ⟨shape, []⟩ cost ∧
      (1 + 2 * cost : ℝ) ≤ 15 + 30 * Real.logb 2 (mass weight t / weight (t.inorder[rank.val]'rank.isLt)) := by
  have inside : rank.val < shape.size := by
    rw [layout_size layout, ← Representation.Bridge.inorder_length]
    exact rank.isLt
  obtain ⟨visited, tree, key, outward, inward⟩ := Pointer.search_walk shape rank.val inside
  refine ⟨visited, Tree.depth shape rank.val, tree, key, outward, inward, ?_⟩
  have bound := layout_depth_at layout rank
  linarith

end RotationBST.HeavyPath.Recursive.History
