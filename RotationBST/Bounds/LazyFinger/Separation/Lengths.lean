module

public import RotationBST.Bounds.LazyFinger.Separation.Unbounded
public import RotationBST.Bounds.LazyFinger.Diagonal

@[expose] public section
namespace RotationBST.LazyFinger

theorem pairSequenceAtLength_length (n m : Nat) :
    (pairSequenceAtLength n m).length = m := by
  simp only [pairSequenceAtLength, List.length_append, pairSequence_length, List.length_replicate]
  have split := Nat.mod_add_div m (2 * n * n)
  nlinarith

theorem pairSequenceAtLength_valid (n m : Nat) (positive : 0 < n) :
    ∀ x ∈ pairSequenceAtLength n m, x < n := by
  intro x member
  rcases List.mem_append.mp member with member | member
  · exact pairSequence_valid n _ x member
  · have key : x = 0 := (List.mem_replicate.mp member).2
    omega

/-- Appending requests cannot lower the cost in a fixed lazy-finger tree. -/
theorem cost_le_append (t : Tree) (xs ys : List Nat) : cost t xs ≤ cost t (xs ++ ys) := by
  cases t with
  | nil => simp [cost]
  | node l r => change costFrom _ _ xs ≤ costFrom _ _ (xs ++ ys); rw [costFrom_append]; omega

/-- A repeated key needs at most one physical reshape and then constant work
per request. An empty suffix performs no reshape. -/
theorem repeat_dynamic (s : Tree) (x count : Nat) (valid : x < s.size) :
    ∃ t k, t.size = s.size ∧ Pointer.Execution s (List.replicate count x) t k ∧
      k ≤ 16 * s.size + 3 * count := by
  cases count with
  | zero => exact ⟨s, 0, rfl, .nil, Nat.zero_le _⟩
  | succ count =>
    obtain ⟨t, size, depth, _⟩ := pair_shallow_tree s.size x x valid valid
    obtain ⟨k, execution, upper⟩ := Pointer.shallow_execution t (List.replicate (count + 1) x) 1
      (by intro z member; have key := (List.mem_replicate.mp member).2; simpa [key, size] using valid)
      (by intro z member; have key := (List.mem_replicate.mp member).2; simpa [key] using depth)
    obtain ⟨j, startup, trace⟩ := Pointer.reshape s t size.symm
    simp only [List.replicate_succ] at execution ⊢
    refine ⟨t, j + k, size, execution.prepend trace, ?_⟩
    simp only [List.length_replicate] at upper
    omega

/-- The padding is shorter than one all-pairs layer. Long blocks absorb both
that padding and its explicitly charged reshaping cost. -/
theorem pairSequenceAtLength_dynamic (s : Tree) (m : Nat) (positive : 0 < s.size)
    (long : 16 * s.size ≤ m / (2 * s.size * s.size)) :
    ∃ t k, t.size = s.size ∧ Pointer.Execution s (pairSequenceAtLength s.size m) t k ∧
      k ≤ 14 * (m / (2 * s.size * s.size)) * s.size * s.size := by
  obtain ⟨middle, k, size, first, upper⟩ := pairSequence_dynamic_long s _ long
  obtain ⟨t, j, finalSize, last, tailBound⟩ := repeat_dynamic middle 0
    (m % (2 * s.size * s.size)) (by omega)
  rw [size] at tailBound
  have remainder := Nat.mod_lt m (show 0 < 2 * s.size * s.size by positivity)
  have rounds : 1 ≤ m / (2 * s.size * s.size) := by omega
  have square : 1 ≤ s.size * s.size := by nlinarith
  have bulk := Nat.mul_le_mul_right (s.size * s.size) rounds
  have startup := Nat.mul_le_mul_left (m / (2 * s.size * s.size)) square
  refine ⟨t, k + j, finalSize.trans size, first.append last, ?_⟩
  nlinarith

theorem pairSequenceAtLength_lower (t : Tree) (m r : Nat) (large : 2 * 7 ^ r ≤ t.size) :
    (m / (2 * t.size * t.size)) * (r + 1) * t.size * t.size ≤
      2 * cost t (pairSequenceAtLength t.size m) := by
  have lower := pairSequence_lower t (m / (2 * t.size * t.size)) r large
  exact lower.trans (Nat.mul_le_mul_left 2 (cost_le_append t _ _))

/-- Every sufficiently large prescribed length admits a lazy/dynamic gap.
The sequence is fixed before the dynamic initial tree is chosen. -/
theorem lazy_dynamic_all_lengths (C : Nat) (allowance : Nat → Nat) :
    ∃ n threshold, 0 < n ∧ n ≤ threshold ∧ ∀ m, threshold ≤ m →
      ∃ xs, xs.length = m ∧ (∀ x ∈ xs, x < n) ∧
        ∀ s : Tree, s.size = n → ∃ t k, Pointer.Execution s xs t k ∧
          C * k + allowance n < optimalCost n xs := by
  let r := 28 * C + 2
  let n := 2 * 7 ^ r
  let threshold := (16 * n + 2 * allowance n + 1) * (2 * n * n)
  have positive : 0 < n := by dsimp [n]; positivity
  have layer : 0 < 2 * n * n := by positivity
  have thresholdLarge : n ≤ threshold := by dsimp [threshold]; nlinarith
  refine ⟨n, threshold, positive, thresholdLarge, ?_⟩
  intro m long
  have rounds : 16 * n + 2 * allowance n + 1 ≤ m / (2 * n * n) :=
    (Nat.le_div_iff_mul_le layer).mpr long
  have square : 1 ≤ n * n := by nlinarith
  have bulk := Nat.mul_le_mul_left (m / (2 * n * n)) square
  refine ⟨pairSequenceAtLength n m, pairSequenceAtLength_length n m,
    pairSequenceAtLength_valid n m positive, ?_⟩
  intro s size
  obtain ⟨t, k, _, execution, upper⟩ := pairSequenceAtLength_dynamic s m (by omega) (by
    rw [size]; omega)
  rw [size] at execution upper
  obtain ⟨reference, referenceSize, optimum⟩ := optimalCost_attained n (pairSequenceAtLength n m)
  have lower := pairSequenceAtLength_lower reference m r (by rw [referenceSize])
  rw [referenceSize, optimum] at lower
  have paid := Nat.mul_le_mul_left (2 * C) upper
  refine ⟨t, k, execution, ?_⟩
  dsimp [r] at lower
  nlinarith

/-- One family of sequences eventually separates optimal static lazy finger
from a legal dynamic execution by every fixed factor. Its universe and requests
depend only on the length, before the factor or initial tree is quantified. -/
theorem lazy_dynamic_family (allowance : Nat → Nat) :
    ∃ sizes : Nat → Nat, ∃ family : Nat → List Nat,
      (∀ m, 0 < sizes m ∧ (family m).length = m ∧
        (∀ x ∈ family m, x < sizes m)) ∧
      ∀ C, ∃ threshold, ∀ m, threshold ≤ m →
        ∀ s : Tree, s.size = sizes m → ∃ t k, Pointer.Execution s (family m) t k ∧
          C * k + allowance (sizes m) < optimalCost (sizes m) (family m) := by
  apply sequence_family_of_eventual_witnesses
    (fun C n xs => ∀ s : Tree, s.size = n → ∃ t k, Pointer.Execution s xs t k ∧
      C * k + allowance n < optimalCost n xs)
  · intro a b n xs factor gap s size
    obtain ⟨t, k, execution, bound⟩ := gap s size
    exact ⟨t, k, execution, (Nat.add_le_add_right (Nat.mul_le_mul_right k factor) _).trans_lt bound⟩
  · intro C
    obtain ⟨n, threshold, positive, _, witnesses⟩ := lazy_dynamic_all_lengths C allowance
    exact ⟨n, threshold, positive, witnesses⟩

end RotationBST.LazyFinger
