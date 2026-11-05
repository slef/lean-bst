module

public import RotationBST.Bounds.LazyFinger.AncestorDistance
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

theorem distance_triangle (t : Tree) (x y z : Nat)
    (hx : x < t.size) (hy : y < t.size) (hz : z < t.size) :
    distance t x z ≤ distance t x y + distance t y z := by
  have realBound : (distance t x z : ℝ) ≤ (distance t x y : ℝ) + distance t y z := by
    have hxy := distance_ancestor_sum t 0 x y ⟨Nat.zero_le _, by simpa using hx⟩
      ⟨Nat.zero_le _, by simpa using hy⟩
    have hyz := distance_ancestor_sum t 0 y z ⟨Nat.zero_le _, by simpa using hy⟩
      ⟨Nat.zero_le _, by simpa using hz⟩
    have hxz := distance_ancestor_sum t 0 x z ⟨Nat.zero_le _, by simpa using hx⟩
      ⟨Nat.zero_le _, by simpa using hz⟩
    simp only [Nat.sub_zero] at hxy hyz hxz
    rw [hxy, hyz, hxz, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    by_cases hax : a ∈ t.searchPath 0 x <;>
      by_cases hay : a ∈ t.searchPath 0 y <;>
      by_cases haz : a ∈ t.searchPath 0 z <;> norm_num [hax, hay, haz]
  exact_mod_cast realBound

theorem costFrom_change_start (t : Tree) (p q : Nat) (xs : List Nat)
    (hp : p < t.size) (hq : q < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    costFrom t p xs ≤ distance t p q + costFrom t q xs := by
  cases xs with
  | nil => simp [costFrom]
  | cons x xs =>
    have hx := valid x (by simp)
    have h := distance_triangle t p q x hp hq hx
    simp only [costFrom]
    omega

theorem depth_le_size (t : Tree) (x : Nat) : Tree.depth t x ≤ t.size := by
  induction t generalizing x with
  | nil => simp [Tree.depth, Tree.size]
  | node l r ihl ihr =>
    simp only [Tree.depth]
    split
    · have := ihl x; simp only [Tree.size]; omega
    · split
      · exact Nat.zero_le _
      · have := ihr (x - l.size - 1); simp only [Tree.size]; omega

theorem distance_from_root (l r : Tree) (x : Nat) :
    distance (.node l r) l.size x = Tree.depth (.node l r) x := by
  simp [distance, Tree.depth]

/-- Starting at any existing key instead of the root changes total cost by at
most the number of keys. Initialization is paid once, not once per request. -/
theorem initialization_bounds (t : Tree) (p : Nat) (xs : List Nat)
    (hp : p < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    costFrom t p xs ≤ t.size + cost t xs ∧ cost t xs ≤ t.size + costFrom t p xs := by
  cases t with
  | nil => simp [Tree.size] at hp
  | node l r =>
    have hroot : l.size < (Tree.node l r).size := by simp [Tree.size]; omega
    have h₁ := costFrom_change_start (.node l r) p l.size xs hp hroot valid
    have h₂ := costFrom_change_start (.node l r) l.size p xs hroot hp valid
    rw [distance_symm, distance_from_root] at h₁
    rw [distance_from_root] at h₂
    have hd := depth_le_size (.node l r) p
    simp only [cost]
    constructor <;> omega

end RotationBST.LazyFinger
