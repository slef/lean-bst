module

public import RotationBST.Bounds.LazyFinger.Neighborhood.Abstract
public import RotationBST.Bounds.LazyFinger.Separation.Abstract
public import RotationBST.Models.Pointer.Abstract

@[expose] public section
namespace RotationBST.Tests.LazyFingerSeparation

private def leaf : Tree := .node .nil .nil
private def two : Tree := .node .nil leaf
private def balanced : Tree := .node (.node leaf leaf) (.node leaf leaf)

-- An interior node has both children and its parent in the radius-one ball.
example : LazyFinger.ball balanced 1 1 = {0, 1, 2, 3} := by decide
example : LazyFinger.ball balanced 1 0 = {1} := by decide
example : (LazyFinger.ball balanced 1 1).card ≤ 7 :=
  LazyFinger.Neighborhood.Results.cardinality balanced 1 1 (by decide)
example : (LazyFinger.ball leaf 0 0).card ≤ 1 :=
  LazyFinger.Neighborhood.Results.cardinality leaf 0 0 (by decide)

-- The all-pairs witness includes diagonal pairs, both orders, and block boundaries.
example : LazyFinger.pairSequence 2 2 =
    [0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1] := by decide
example : LazyFinger.cost two (LazyFinger.pairSequence 2 2) = 23 := by decide
example : (LazyFinger.pairSequence 3 4).length = 72 :=
  LazyFinger.Separation.Results.length 3 4
example : ∀ x ∈ LazyFinger.pairSequence 3 4, x < 3 :=
  LazyFinger.Separation.Results.valid 3 4

-- Two-key preparation retains intervening and exterior ranks, in either order.
example : ∃ t : Tree, t.size = 7 ∧ Tree.depth t 0 ≤ 1 ∧ Tree.depth t 6 ≤ 1 :=
  LazyFinger.pair_shallow_tree 7 0 6 (by decide) (by decide)
example : ∃ t : Tree, t.size = 7 ∧ Tree.depth t 5 ≤ 1 ∧ Tree.depth t 1 ≤ 1 :=
  LazyFinger.pair_shallow_tree 7 5 1 (by decide) (by decide)
example : ∃ t : Tree, t.size = 7 ∧ Tree.depth t 4 ≤ 1 ∧ Tree.depth t 4 ≤ 1 :=
  LazyFinger.pair_shallow_tree 7 4 4 (by decide) (by decide)

-- The same sequence has checked lower and upper bounds in physical models.
example : 8 ≤ 2 * LazyFinger.cost two (LazyFinger.pairSequence 2 2) :=
  LazyFinger.Separation.Results.lazy_lower two 2 0 (by decide)
example : ∃ t k, t.size = 2 ∧ Pointer.Execution two (LazyFinger.pairSequence 2 32) t k ∧ k ≤ 896 :=
  LazyFinger.Separation.Results.dynamic_linear two 32 (by decide)

-- Empty domains and zero rounds do not require fabricated requests or fingers.
example : ∃ t k, t.size = 0 ∧ Pointer.Execution .nil [] t k ∧ k ≤ 0 :=
  LazyFinger.Separation.Results.dynamic_upper .nil 4
example : ∃ t k, t.size = 2 ∧ Pointer.Execution two [] t k ∧ k ≤ 128 :=
  LazyFinger.Separation.Results.dynamic_upper two 0

-- The separation is uniform over the prescribed dynamic initial shape and
-- survives a superlinear startup allowance, not merely a favorable initialization.
example (C : Nat) :
    ∃ n xs, 0 < n ∧ n ≤ xs.length ∧ (∀ x ∈ xs, x < n) ∧
      ∀ s : Tree, s.size = n → ∃ t k, Pointer.Execution s xs t k ∧
        C * k + n ^ 3 < LazyFinger.optimalCost n xs :=
  LazyFinger.Separation.Results.with_startup C (fun n => n ^ 3)

-- Exact lengths include empty padding, a partial layer, and odd lengths.
example : LazyFinger.pairSequenceAtLength 2 0 = [] := by decide
example : LazyFinger.pairSequenceAtLength 2 3 = [0, 0, 0] := by decide
example : LazyFinger.pairSequenceAtLength 2 8 = [0, 0, 0, 1, 1, 0, 1, 1] := by decide
example : LazyFinger.pairSequenceAtLength 2 9 = [0, 0, 0, 1, 1, 0, 1, 1, 0] := by decide
example : (LazyFinger.pairSequenceAtLength 2 257).length = 257 :=
  LazyFinger.Separation.Results.prescribed_length 2 257
example : ∀ x ∈ LazyFinger.pairSequenceAtLength 2 257, x < 2 :=
  LazyFinger.Separation.Results.prescribed_valid 2 257 (by decide)
example : 4 ≤ 2 * LazyFinger.cost two (LazyFinger.pairSequenceAtLength 2 9) :=
  LazyFinger.Separation.Results.prescribed_lower two 9 0 (by decide)

-- The dynamic bound covers both a layer boundary and a nonempty odd suffix.
example : ∃ t k, t.size = 2 ∧ Pointer.Execution two (LazyFinger.pairSequenceAtLength 2 256) t k ∧
    k ≤ 1792 := LazyFinger.Separation.Results.prescribed_dynamic two 256 (by decide) (by decide)
example : ∃ t k, t.size = 2 ∧ Pointer.Execution two (LazyFinger.pairSequenceAtLength 2 257) t k ∧
    k ≤ 1792 := LazyFinger.Separation.Results.prescribed_dynamic two 257 (by decide) (by decide)

-- The caller chooses a length after the universe and threshold are fixed.
example (C : Nat) :
    ∃ n threshold, 0 < n ∧ n ≤ threshold ∧
      ∃ xs, xs.length = threshold + n + 1 ∧ (∀ x ∈ xs, x < n) ∧
        ∀ s : Tree, s.size = n → ∃ t k, Pointer.Execution s xs t k ∧
          C * k + n ^ 3 < LazyFinger.optimalCost n xs := by
  obtain ⟨n, threshold, positive, large, lengths⟩ :=
    LazyFinger.Separation.Results.all_lengths C (fun n => n ^ 3)
  exact ⟨n, threshold, positive, large, lengths (threshold + n + 1) (by omega)⟩

-- Quantifying the factor after the family asserts a growing ratio, rather
-- than selecting a new family for each factor.
example : ∃ sizes : Nat → Nat, ∃ requests : Nat → List Nat,
    (∀ m, 0 < sizes m ∧ (requests m).length = m ∧ (∀ x ∈ requests m, x < sizes m)) ∧
    ∀ C, ∃ threshold, ∀ m, threshold ≤ m → ∀ s : Tree, s.size = sizes m →
      ∃ t k, Pointer.Execution s (requests m) t k ∧
        C * k < LazyFinger.optimalCost (sizes m) (requests m) := by
  simpa only [Nat.add_zero] using LazyFinger.Separation.Results.family (fun _ => 0)

-- Zero-step instruction encodings cannot reach two different keys.
example (a : Pointer.Config) (keys : Finset Nat)
    (reachable : ∀ x ∈ keys, ∃ b k, Pointer.Trace a b k ∧ k ≤ 0 ∧ b.key? = some x) :
    keys.card ≤ 1 := Pointer.Results.reachable_keys a 0 keys reachable

end RotationBST.Tests.LazyFingerSeparation
