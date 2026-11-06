module

public import RotationBST.Structures.HeavyPath.Finger.SideDepth
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree

theorem build_ranks {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    RanksSatisfy (fun rank target => (Tree.depth (build weight cs left right).tree rank : ℝ) ≤
      15 + 15 * Real.logb 2 (HeavyPath.mass weight (plug cs (.node left key right)) / weight target))
      0 (plug cs (.node left key right)).inorder := by
  let p := build weight cs left right
  let W := HeavyPath.mass weight (plug cs (.node left key right))
  let P := fun rank target => (Tree.depth p.tree rank : ℝ) ≤ 15 + 15 * Real.logb 2 (W / weight target)
  let below := (lowerFrames cs).flatMap lowerBlock ++ left.inorder
  let above := right.inorder ++ (upperFrames cs).flatMap upperBlock
  have focus := (context_positive cs (.node left key right) positive).1
  obtain ⟨valid, lowerFringe, upperFringe⟩ := build_valid_fringe positive
  change p.Valid at valid
  change p.lower.decode.mirror.fringe = _ at lowerFringe
  change p.upper.decode.fringe = _ at upperFringe
  have partition := build_mass positive
  have sourceMass : p.mass ≤ W := by
    change weight key + p.mass = W at partition
    have own := focus.2.1
    linarith
  have frames : ∀ f ∈ cs, Positive weight (framePayload f) ∧ 0 < weight (frameKey f) := by
    intro f hf
    exact ⟨payload_positive cs (.node left key right) positive hf,
      context_key_positive cs (.node left key right) positive hf⟩
  have inorder : (plug cs (.node left key right)).inorder = below ++ ([key] ++ above) := by
    rw [context_inorder]
    simp only [below, above, LabelledTree.inorder, List.append_assoc, List.cons_append, List.nil_append]
  have lowerLength : below.length = p.lower.decode.tree.mirror.size := by
    rw [(build_side_sizes positive).1]
    simp only [below, List.length_append, Representation.Bridge.inorder_length]
  have lowerBound : RanksSatisfy P 0 below := by
    apply lower_ranks valid sourceMass focus.1 le_rfl
      (fun f hf => frames f (lowerFrames_mem hf)) (before := []) (after := p.upper.decode.fringe)
    simp only [WeightedTree.fringe, lowerFringe, List.nil_append]
  have upperBound : RanksSatisfy P (p.lower.decode.tree.mirror.size + 1) above := by
    have bound := upper_ranks valid sourceMass focus.2.2 (carry := 0) le_rfl
      (fun f hf => frames f (upperFrames_mem (List.mem_reverse.mp hf)))
      (before := p.lower.decode.mirror.fringe) (after := [])
      (by simp only [WeightedTree.fringe, upperFringe, List.append_nil])
    simpa only [fringeSpan_fringe, mirror_tree, List.reverse_reverse] using bound
  have rootBound : P p.lower.decode.tree.mirror.size key := by
    have member : key ∈ (plug cs (.node left key right)).inorder := by rw [inorder]; simp
    obtain ⟨keyPositive, keyMass⟩ := inorder_weight positive member
    have logarithm : 0 ≤ Real.logb 2 (W / weight key) := by
      apply Real.logb_nonneg (by norm_num)
      exact (le_div_iff₀ keyPositive).mpr (by simpa only [one_mul] using keyMass)
    dsimp only [P]
    have rootDepth : Tree.depth p.tree p.lower.decode.tree.mirror.size = 0 := by
      simp [Pair.tree, Tree.depth]
    rw [rootDepth]
    norm_num only [Nat.cast_zero]
    linarith
  change RanksSatisfy P 0 _
  rw [inorder]
  apply RanksSatisfy.append lowerBound
  apply RanksSatisfy.append
  · apply RanksSatisfy.singleton
    simpa only [Nat.zero_add, lowerLength] using rootBound
  · simpa only [Nat.zero_add, lowerLength, List.length_singleton] using upperBound

/-- Every original occurrence has weighted logarithmic depth at an arbitrary
source cursor. This theorem does not assume that its ancestor path is heavy. -/
theorem build_depth {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right)))
    {before after : List α} {target : α}
    (occurrence : (plug cs (.node left key right)).inorder = before ++ target :: after) :
    (Tree.depth (build weight cs left right).tree before.length : ℝ) ≤
      15 + 15 * Real.logb 2 (HeavyPath.mass weight (plug cs (.node left key right)) / weight target) := by
  simpa only [Nat.zero_add] using build_ranks positive before target after occurrence

theorem build_depth_at {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right)))
    (rank : Fin (plug cs (.node left key right)).inorder.length) :
    (Tree.depth (build weight cs left right).tree rank.val : ℝ) ≤
      15 + 15 * Real.logb 2 (HeavyPath.mass weight (plug cs (.node left key right)) /
        weight ((plug cs (.node left key right)).inorder[rank.val]'rank.isLt)) := by
  have split : (plug cs (.node left key right)).inorder =
      (plug cs (.node left key right)).inorder.take rank.val ++
      (plug cs (.node left key right)).inorder[rank.val] ::
      (plug cs (.node left key right)).inorder.drop (rank.val + 1) := by
    rw [← List.drop_eq_getElem_cons rank.isLt, List.take_append_drop]
  have bound := build_depth positive split
  simpa only [List.length_take, Nat.min_eq_left rank.isLt.le] using bound

theorem build_unit_depth {α : Type} (cs : List (Frame α)) (left right : LabelledTree α) (key : α)
    (rank : Nat) (valid : rank < (plug cs (.node left key right)).erase.size) :
    (Tree.depth (build (fun _ => 1) cs left right).tree rank : ℝ) ≤
      15 + 15 * Real.logb 2 ((plug cs (.node left key right)).erase.size : ℝ) := by
  have inside : rank < (plug cs (.node left key right)).inorder.length := by
    simpa only [Representation.Bridge.inorder_length] using valid
  simpa only [unit_mass, div_one] using
    build_depth_at (unit_positive (plug cs (.node left key right))) ⟨rank, inside⟩

theorem build_search_walk {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right)))
    (rank : Fin (plug cs (.node left key right)).inorder.length) :
    ∃ (visited : Pointer.Config) (cost : Nat),
      visited.tree = (build weight cs left right).tree ∧ visited.key? = some rank.val ∧
      Pointer.Trace ⟨(build weight cs left right).tree, []⟩ visited cost ∧
      Pointer.Trace visited ⟨(build weight cs left right).tree, []⟩ cost ∧
      (1 + 2 * cost : ℝ) ≤ 31 + 30 * Real.logb 2
        (HeavyPath.mass weight (plug cs (.node left key right)) /
          weight ((plug cs (.node left key right)).inorder[rank.val]'rank.isLt)) := by
  have inside : rank.val < (build weight cs left right).tree.size := by
    rw [build_size positive, ← Representation.Bridge.inorder_length]
    exact rank.isLt
  obtain ⟨visited, tree, key, outward, inward⟩ := Pointer.search_walk (build weight cs left right).tree rank.val inside
  refine ⟨visited, Tree.depth (build weight cs left right).tree rank.val, tree, key, outward, inward, ?_⟩
  have bound := build_depth_at positive rank
  linarith

end RotationBST.HeavyPath.Finger
