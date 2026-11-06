module

public import RotationBST.Structures.HeavyPath.Finger.History.SideDepth
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree Recursive.History

theorem state_ranks {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    {s : State α} (valid : Valid weight cs left key right s) :
    RanksSatisfy (fun rank target => (Tree.depth s.pair.tree rank : ℝ) ≤
      15 + 15 * Real.logb 2 (HeavyPath.mass weight (plug cs (.node left key right)) / weight target))
      0 (plug cs (.node left key right)).inorder := by
  let p := s.pair
  let W := HeavyPath.mass weight (plug cs (.node left key right))
  let P := fun rank target => (Tree.depth p.tree rank : ℝ) ≤ 15 + 15 * Real.logb 2 (W / weight target)
  let below := (Recursive.History.lower s.ancestors).flatMap Entry.lowerBlock ++ left.inorder
  let above := right.inorder ++ (Recursive.History.upper s.ancestors).flatMap Entry.upperBlock
  have positive := valid.positive
  have focus := (context_positive cs (.node left key right) positive).1
  have pairValid : p.Valid := valid.pair
  have lowerFringe := valid.lower
  have upperFringe := valid.upper
  change p.lower.decode.mirror.fringe = _ at lowerFringe
  change p.upper.decode.fringe = _ at upperFringe
  have partition := state_mass valid
  have sourceMass : p.mass ≤ W := by
    change weight key + p.mass = W at partition
    have own := focus.2.1
    linarith
  have frames : ∀ e ∈ s.ancestors, Positive weight (framePayload e.source) ∧ 0 < weight (frameKey e.source) :=
    fun _ he => frame_positive valid he
  have inorder : (plug cs (.node left key right)).inorder = below ++ ([key] ++ above) := by
    rw [context_inorder valid.context]
    simp only [below, above, LabelledTree.inorder, List.append_assoc, List.cons_append, List.nil_append]
  have lowerLength : below.length = p.lower.decode.tree.mirror.size := by
    rw [(state_side_sizes valid).1]
    simp only [below, List.length_append, Representation.Bridge.inorder_length]
  have lowerBound : RanksSatisfy P 0 below := by
    apply lower_ranks pairValid sourceMass valid.leftLayout le_rfl
      (fun e he => frames e (lower_mem he))
      (fun e he => valid.children e (lower_mem he)) (before := []) (after := p.upper.decode.fringe)
    simp only [WeightedTree.fringe, lowerFringe, List.nil_append]
  have upperBound : RanksSatisfy P (p.lower.decode.tree.mirror.size + 1) above := by
    have bound := upper_ranks pairValid sourceMass valid.rightLayout (carry := 0) le_rfl
      (fun e he => frames e (upper_mem (List.mem_reverse.mp he)))
      (fun e he => valid.children e (upper_mem (List.mem_reverse.mp he)))
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
theorem state_depth {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    {s : State α} (valid : Valid weight cs left key right s)
    {before after : List α} {target : α}
    (occurrence : (plug cs (.node left key right)).inorder = before ++ target :: after) :
    (Tree.depth s.pair.tree before.length : ℝ) ≤
      15 + 15 * Real.logb 2 (HeavyPath.mass weight (plug cs (.node left key right)) / weight target) := by
  simpa only [Nat.zero_add] using state_ranks valid before target after occurrence

theorem state_depth_at {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    {s : State α} (valid : Valid weight cs left key right s)
    (rank : Fin (plug cs (.node left key right)).inorder.length) :
    (Tree.depth s.pair.tree rank.val : ℝ) ≤
      15 + 15 * Real.logb 2 (HeavyPath.mass weight (plug cs (.node left key right)) /
        weight ((plug cs (.node left key right)).inorder[rank.val]'rank.isLt)) := by
  have split : (plug cs (.node left key right)).inorder =
      (plug cs (.node left key right)).inorder.take rank.val ++
      (plug cs (.node left key right)).inorder[rank.val] ::
      (plug cs (.node left key right)).inorder.drop (rank.val + 1) := by
    rw [← List.drop_eq_getElem_cons rank.isLt, List.take_append_drop]
  have bound := state_depth valid split
  simpa only [List.length_take, Nat.min_eq_left rank.isLt.le] using bound

theorem state_search_walk {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    {s : State α} (valid : Valid weight cs left key right s)
    (rank : Fin (plug cs (.node left key right)).inorder.length) :
    ∃ (visited : Pointer.Config) (cost : Nat),
      visited.tree = s.pair.tree ∧ visited.key? = some rank.val ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ visited cost ∧
      Pointer.Trace visited ⟨s.pair.tree, []⟩ cost ∧
      (1 + 2 * cost : ℝ) ≤ 31 + 30 * Real.logb 2
        (HeavyPath.mass weight (plug cs (.node left key right)) /
          weight ((plug cs (.node left key right)).inorder[rank.val]'rank.isLt)) := by
  have inside : rank.val < s.pair.tree.size := by
    rw [state_size valid, ← Representation.Bridge.inorder_length]
    exact rank.isLt
  obtain ⟨visited, tree, key, outward, inward⟩ := Pointer.search_walk s.pair.tree rank.val inside
  refine ⟨visited, Tree.depth s.pair.tree rank.val, tree, key, outward, inward, ?_⟩
  have bound := state_depth_at valid rank
  linarith

end RotationBST.HeavyPath.Finger.History
