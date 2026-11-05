module

public import RotationBST.Bounds.LazyFinger.Separation.Sequence
public import RotationBST.Models.Pointer.Execution
public import RotationBST.Models.Pointer.Reshape
public import RotationBST.Bounds.LazyFinger.Optimal

@[expose] public section
namespace RotationBST.LazyFinger

/-- Two prescribed ranks can both lie at depth at most one in some tree on the
whole universe. The other keys remain present, in their original order. -/
theorem pair_shallow_tree (n x y : Nat) (hx : x < n) (hy : y < n) :
    ∃ t : Tree, t.size = n ∧ Tree.depth t x ≤ 1 ∧ Tree.depth t y ≤ 1 := by
  have ordered : ∀ a b, a < n → b < n → a ≤ b →
      ∃ t : Tree, t.size = n ∧ Tree.depth t a ≤ 1 ∧ Tree.depth t b ≤ 1 := by
    intro a b ha hb order
    by_cases equal : a = b
    · subst b
      obtain ⟨l, sl, _⟩ := optimalCost_attained a []
      obtain ⟨r, sr, _⟩ := optimalCost_attained (n - a - 1) []
      refine ⟨.node l r, by simp only [Tree.size, sl, sr]; omega, ?_, ?_⟩ <;>
        simp only [Tree.depth, sl, Nat.lt_irrefl, ↓reduceIte, Nat.zero_le]
    · obtain ⟨l, sl, _⟩ := optimalCost_attained a []
      obtain ⟨m, sm, _⟩ := optimalCost_attained (b - a - 1) []
      obtain ⟨r, sr, _⟩ := optimalCost_attained (n - b - 1) []
      have positive : a < b := by omega
      refine ⟨.node l (.node m r), by simp only [Tree.size, sl, sm, sr]; omega, ?_, ?_⟩
      · simp only [Tree.depth, sl, Nat.lt_irrefl, ↓reduceIte, Nat.zero_le]
      · simp only [Tree.depth, sl, sm, Nat.not_lt.mpr order,
          Ne.symm equal, Nat.lt_irrefl, ↓reduceIte]
        omega
  by_cases order : x ≤ y
  · exact ordered x y hx hy order
  · obtain ⟨t, size, first, second⟩ := ordered y x hy hx (by omega)
    exact ⟨t, size, second, first⟩

/-- A dynamic BST reshapes once for an alternating pair and then serves every
request at depth at most one. The full reshaping cost is charged explicitly. -/
theorem pairBlock_dynamic (s : Tree) (x y rounds : Nat) (hx : x < s.size) (hy : y < s.size) :
    ∃ t k, t.size = s.size ∧ Pointer.Execution s (pairBlock x y rounds) t k ∧
      k ≤ 16 * s.size + 6 * rounds := by
  cases rounds with
  | zero => exact ⟨s, 0, rfl, .nil, Nat.zero_le _⟩
  | succ rounds =>
    obtain ⟨t, size, dx, dy⟩ := pair_shallow_tree s.size x y hx hy
    have valid := pairBlock_valid s.size x y (rounds + 1) hx hy
    have shallow : ∀ z ∈ pairBlock x y (rounds + 1), Tree.depth t z ≤ 1 := by
      have members : ∀ r z, z ∈ pairBlock x y r → z = x ∨ z = y := by
        intro r
        induction r with
        | zero => simp [pairBlock]
        | succ r ih => intro z hz; simp only [pairBlock, List.mem_cons] at hz; aesop
      intro z hz
      rcases members _ z hz with rfl | rfl
      · exact dx
      · exact dy
    obtain ⟨k, run, bound⟩ := Pointer.shallow_execution t (pairBlock x y (rounds + 1)) 1
      (by simpa only [size] using valid) shallow
    obtain ⟨j, startup, trace⟩ := Pointer.reshape s t size.symm
    refine ⟨t, j + k, size, run.prepend trace, ?_⟩
    rw [pairBlock_length] at bound
    omega

/-- Execute all pair blocks, allowing the physical tree to change between them.
Each block pays for a real pointer reshape, so no reference-tree switch is free. -/
theorem pairBlocks_dynamic (s : Tree) (pairs : List (Nat × Nat)) (rounds : Nat)
    (valid : ∀ pair ∈ pairs, pair.1 < s.size ∧ pair.2 < s.size) :
    ∃ t k, t.size = s.size ∧ Pointer.Execution s (pairBlocks pairs rounds) t k ∧
      k ≤ pairs.length * (16 * s.size + 6 * rounds) := by
  induction pairs generalizing s with
  | nil => exact ⟨s, 0, rfl, .nil, by simp⟩
  | cons pair pairs ih =>
    have hp := valid pair (by simp)
    obtain ⟨middle, k, size, first, firstCost⟩ := pairBlock_dynamic s pair.1 pair.2 rounds hp.1 hp.2
    obtain ⟨t, m, finalSize, rest, restCost⟩ := ih middle (by
      intro p member
      simpa only [size] using valid p (by simp [member]))
    refine ⟨t, k + m, finalSize.trans size, first.append rest, ?_⟩
    simp only [size] at restCost
    simp only [List.length_cons]
    nlinarith

theorem pairSequence_dynamic (s : Tree) (rounds : Nat) :
    ∃ t k, t.size = s.size ∧ Pointer.Execution s (pairSequence s.size rounds) t k ∧
      k ≤ s.size * s.size * (16 * s.size + 6 * rounds) := by
  have run := pairBlocks_dynamic s
    ((List.range s.size).flatMap fun x => (List.range s.size).map fun y => (x, y)) rounds (by
      intro pair member
      obtain ⟨x, hx, hp⟩ := List.mem_flatMap.mp member
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
      exact ⟨List.mem_range.mp hx, List.mem_range.mp hy⟩)
  simpa [pairSequence, List.length_flatMap, List.sum_replicate] using run

end RotationBST.LazyFinger
