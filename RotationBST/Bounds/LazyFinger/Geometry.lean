module

public import RotationBST.Bounds.LazyFinger.Proofs

@[expose] public section
namespace RotationBST.LazyFinger

/-- Avoiding natural-number subtraction makes the exact LCA identity useful
without side conditions. For existing keys it is the ordinary edge metric. -/
theorem distance_add_twice_lca (t : Tree) (x y : Nat) :
    distance t x y + 2 * lcaDepth t x y =
      Tree.depth t x + Tree.depth t y := by
  induction t generalizing x y with
  | nil => simp [distance, lcaDepth, Tree.depth]
  | node l r ihl ihr =>
    simp only [distance, lcaDepth]
    split
    · rename_i h
      have := ihl x y
      simp [Tree.depth, h.1, h.2]
      omega
    · rename_i hleft
      split
      · rename_i h
        have := ihr (x - l.size - 1) (y - l.size - 1)
        simp [Tree.depth, Nat.not_lt.mpr (Nat.le_of_lt h.1),
          Nat.not_lt.mpr (Nat.le_of_lt h.2), Nat.ne_of_gt h.1, Nat.ne_of_gt h.2]
        omega
      · rename_i hright
        simp

theorem lcaDepth_le_left (t : Tree) (x y : Nat) :
    lcaDepth t x y ≤ Tree.depth t x := by
  induction t generalizing x y with
  | nil => simp [lcaDepth, Tree.depth]
  | node l r ihl ihr =>
    simp only [lcaDepth]
    split
    · rename_i h
      simpa [Tree.depth, h.1] using Nat.add_le_add_right (ihl x y) 1
    · split
      · rename_i h
        simpa [Tree.depth, Nat.not_lt.mpr (Nat.le_of_lt h.1), Nat.ne_of_gt h.1]
          using Nat.add_le_add_right (ihr (x - l.size - 1) (y - l.size - 1)) 1
      · exact Nat.zero_le _

theorem lcaDepth_symm (t : Tree) (x y : Nat) : lcaDepth t x y = lcaDepth t y x := by
  have h := distance_add_twice_lca t x y
  have h' := distance_add_twice_lca t y x
  rw [distance_symm t y x] at h'
  omega

theorem distance_eq_depths_sub_lca (t : Tree) (x y : Nat) :
    distance t x y = Tree.depth t x + Tree.depth t y - 2 * lcaDepth t x y := by
  have := distance_add_twice_lca t x y
  omega

theorem depth_eq_zero_iff (l r : Tree) (x : Nat) :
    Tree.depth (.node l r) x = 0 ↔ x = l.size := by
  unfold Tree.depth
  split
  · omega
  · split <;> omega

/-- Distinct existing keys are separated by a positive number of moves. -/
theorem distance_eq_zero_iff (t : Tree) (x y : Nat)
    (hx : x < t.size) (hy : y < t.size) : distance t x y = 0 ↔ x = y := by
  constructor
  · induction t generalizing x y with
    | nil => simp [Tree.size] at hx
    | node l r ihl ihr =>
      simp only [distance]
      split
      · rename_i h
        exact fun hz => ihl x y h.1 h.2 hz
      · split
        · rename_i h
          intro hz
          have hxr : x - l.size - 1 < r.size := by simp only [Tree.size] at hx; omega
          have hyr : y - l.size - 1 < r.size := by simp only [Tree.size] at hy; omega
          have := ihr _ _ hxr hyr hz
          omega
        · intro hz
          have hdx : Tree.depth (.node l r) x = 0 := by omega
          have hdy : Tree.depth (.node l r) y = 0 := by omega
          exact (depth_eq_zero_iff l r x).mp hdx |>.trans ((depth_eq_zero_iff l r y).mp hdy).symm
  · rintro rfl
    exact distance_self t x hx

end RotationBST.LazyFinger
