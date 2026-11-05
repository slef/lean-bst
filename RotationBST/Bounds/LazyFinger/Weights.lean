module

public import RotationBST.Bounds.LazyFinger.Geometry
public import RotationBST.Bounds.StaticTree.Weights
public import RotationBST.Bounds.WeightedFinger.Intervals

/-! Tree-to-weights direction of Bose–Douïeb–Iacono–Langerman,
*The Power and Limitations of Static Binary Search Trees with Lazy Finger*,
arXiv:1304.6897, §3. Reuse the static entropy code weights `4^(-(depth+1))`.
Their extra uniform factor of `1/4` cancels from all weighted-finger quotients.
The proof descends to the LCA by interval translation and scale invariance,
then uses the already checked total-mass estimate. -/

@[expose] public section
namespace RotationBST.LazyFinger
open WeightedFinger

/-- When the interval stays in the left child all weights acquire the same
factor, which cancels in the weighted-finger quotient. -/
theorem tree_charge_left (l r : Tree) (x y : Nat) (hx : x < l.size) (hy : y < l.size) :
    charge (StaticTree.weight (.node l r)) x y = charge (StaticTree.weight l) x y := by
  calc
    _ = charge (fun k => (1 / 4 : ℝ) * StaticTree.weight l k) x y := by
      apply charge_congr
      intro k hk
      have hk' : k < l.size := by
        have := (Finset.mem_Icc.mp hk).2
        omega
      rw [StaticTree.weight_left l r k hk']
      ring
    _ = _ := charge_scale _ _ (by norm_num) _ _

theorem tree_charge_right (l r : Tree) (x y : Nat) :
    charge (StaticTree.weight (.node l r)) (l.size + 1 + x) (l.size + 1 + y) =
      charge (StaticTree.weight r) x y := by
  rw [← charge_shift]
  calc
    _ = charge (fun k => (1 / 4 : ℝ) * StaticTree.weight r k) x y := by
      apply charge_congr
      intro k _
      rw [StaticTree.weight_right]
      ring
    _ = _ := charge_scale _ _ (by norm_num) _ _

theorem tree_mass_le_one (t : Tree) (x y : Nat) (hx : x < t.size) (hy : y < t.size) :
    mass (StaticTree.weight t) x y ≤ 1 := by
  apply le_trans _ (StaticTree.weight_sum t)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro k _ _
    exact le_of_lt (StaticTree.weight_pos t k)

/-- A coarse root-based estimate. Applying it only at the LCA gives a
bound by movement distance rather than by the absolute endpoint depths. -/
theorem tree_charge_le_depths (t : Tree) (x y : Nat) (hx : x < t.size) (hy : y < t.size) :
    charge (StaticTree.weight t) x y ≤
      3 + 2 * (Tree.depth t x : ℝ) + 2 * (Tree.depth t y : ℝ) := by
  have hwx := StaticTree.weight_pos t x
  have hwy := StaticTree.weight_pos t y
  have hmin : 0 < min (StaticTree.weight t x) (StaticTree.weight t y) := lt_min hwx hwy
  have hmass : 0 < mass (StaticTree.weight t) x y := by
    apply lt_of_lt_of_le hwx
    apply Finset.single_le_sum (fun k _ => le_of_lt (StaticTree.weight_pos t k))
    exact Finset.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩
  have hratio := div_le_div_of_nonneg_right (tree_mass_le_one t x y hx hy) (le_of_lt hmin)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (div_pos hmass hmin) hratio
  unfold charge
  rcases le_total (StaticTree.weight t x) (StaticTree.weight t y) with h | h
  · rw [min_eq_left h]
    rw [min_eq_left h, StaticTree.log_weight] at hlog
    push_cast at hlog
    have : (0 : ℝ) ≤ Tree.depth t y := Nat.cast_nonneg _
    linarith
  · rw [min_eq_right h]
    rw [min_eq_right h, StaticTree.log_weight] at hlog
    push_cast at hlog
    have : (0 : ℝ) ≤ Tree.depth t x := Nat.cast_nonneg _
    linarith

/-- Tree-to-weights direction of the lazy-finger characterization: one fixed
positive weighting works simultaneously for every pair of existing keys. -/
theorem tree_charge_le_distance (t : Tree) (x y : Nat) (hx : x < t.size) (hy : y < t.size) :
    charge (StaticTree.weight t) x y ≤ 3 + 2 * (distance t x y : ℝ) := by
  induction t generalizing x y with
  | nil => simp [Tree.size] at hx
  | node l r ihl ihr =>
    by_cases hleft : x < l.size ∧ y < l.size
    · rw [tree_charge_left l r x y hleft.1 hleft.2]
      simpa [distance, hleft] using ihl x y hleft.1 hleft.2
    · by_cases hright : l.size < x ∧ l.size < y
      · have hxr : x - l.size - 1 < r.size := by simp only [Tree.size] at hx; omega
        have hyr : y - l.size - 1 < r.size := by simp only [Tree.size] at hy; omega
        have he := tree_charge_right l r (x - l.size - 1) (y - l.size - 1)
        have ex : l.size + 1 + (x - l.size - 1) = x := by omega
        have ey : l.size + 1 + (y - l.size - 1) = y := by omega
        rw [ex, ey] at he
        rw [he]
        simpa [distance, hleft, hright] using ihr _ _ hxr hyr
      · have h := tree_charge_le_depths (.node l r) x y hx hy
        simpa [distance, hleft, hright, Nat.cast_add, mul_add, add_assoc] using h

/-- Sum the pair bound with request charges. The same weights work for every
valid sequence, including repeated keys and any valid initial finger. -/
theorem tree_weighted_cost_le (t : Tree) (p : Nat) (xs : List Nat)
    (hp : p < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    WeightedFinger.costFrom (StaticTree.weight t) p xs ≤ 3 * (costFrom t p xs : ℝ) := by
  induction xs generalizing p with
  | nil => simp [WeightedFinger.costFrom, costFrom]
  | cons x xs ih =>
    have hx : x < t.size := valid x (by simp)
    have hv : ∀ y ∈ xs, y < t.size := fun y hy => valid y (by simp [hy])
    have htail := ih x hx hv
    have hpair := tree_charge_le_distance t p x hp hx
    have hd : (0 : ℝ) ≤ distance t p x := Nat.cast_nonneg _
    simp only [WeightedFinger.costFrom, costFrom, Nat.cast_add, Nat.cast_one]
    linarith

theorem exists_weights_for_tree (t : Tree) :
    ∃ w : Nat → ℝ, (∀ x, 0 < w x) ∧
      (∀ x y, x < t.size → y < t.size →
        WeightedFinger.charge w x y ≤ 3 + 2 * (distance t x y : ℝ)) ∧
      (∀ p xs, p < t.size → (∀ x ∈ xs, x < t.size) →
        WeightedFinger.costFrom w p xs ≤ 3 * (costFrom t p xs : ℝ)) :=
  ⟨StaticTree.weight t, StaticTree.weight_pos t, tree_charge_le_distance t,
    tree_weighted_cost_le t⟩

end RotationBST.LazyFinger
