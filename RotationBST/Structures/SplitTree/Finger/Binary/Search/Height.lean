module

public import RotationBST.Structures.SplitTree.Finger.Binary.Search.Basic

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger
open RotationBST.Tree (depth)

/-- All blocks attached to the finger are balanced subtrees of bounded height. -/
theorem binaryView_blocks {h : Nat} {t : Multiway} (valid : Balanced h t) :
    (∀ block ∈ (binaryView t).spine, ∀ x, depth block x ≤ 2 * h) ∧
      (∀ x, depth (binaryView t).tail x ≤ 2 * h) := by
  induction valid with
  | nil => exact ⟨by simp [binaryView], fun _ => Nat.le_refl _⟩
  | two ha hb ia ib =>
    refine ⟨?_, ?_⟩
    · intro block member x
      simp only [binaryView, List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · have := ia.1 block member x; omega
      · have := ia.2 x; omega
    · intro x
      have := binary_depth hb x
      simp only [binaryView]
      omega
  | three ha hb hc ia ib ic =>
    refine ⟨?_, ?_⟩
    · intro block member x
      simp only [binaryView, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | rfl | rfl
      · have := ia.1 block member x; omega
      · have := ia.2 x; omega
      · have := binary_depth hb x; omega
    · intro x
      have := binary_depth hc x
      simp only [binaryView]
      omega
  | four ha hb hc hd ia ib ic id =>
    refine ⟨?_, ?_⟩
    · intro block member x
      simp only [binaryView, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | rfl | rfl | rfl
      · have := ia.1 block member x; omega
      · have := ia.2 x; omega
      · have := binary_depth hb x; omega
      · have := binary_depth hc x; omega
    · intro x
      have := binary_depth hd x
      simp only [binaryView]
      omega

/-- The bound is independent of any keys appended beyond the current interval. -/
theorem extended_depth_height {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rest : Tree) (rank : Nat) (existsKey : rank < t.size) :
    depth (comb (binaryView t).spine (.node (binaryView t).tail rest)) rank ≤ 5 * h + 1 := by
  obtain ⟨blocks, tail⟩ := binaryView_blocks valid
  have within : rank < (comb (binaryView t).spine (binaryView t).tail).size := by
    rwa [← BinaryView.tree, binaryView_size]
  have bound := comb_depth_extend _ _ rest (2 * h) rank blocks tail within
  have length := binaryView_length valid
  omega

end RotationBST.Geometric.Split.Multiway.Finger
