module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.MultipleTrees.Selection.Abstract
public import RotationBST.Algorithms.MultipleTrees.Cache.Abstract
public import RotationBST.Algorithms.MultipleTrees.AbstractBridge

@[expose] public section
namespace RotationBST.MultipleTrees.Results

/-- The local trees plus the single shared fallback have this exact node count. -/
theorem nodes (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat) :
    (build n capacity positive frequency).nodes = n * min capacity n + n :=
  build_nodes n capacity positive frequency

/-- Four fields per node and one cell per root; no frequency matrix is retained. -/
theorem words (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat) :
    (build n capacity positive frequency).words = 4 * (n * min capacity n + n) + n + 1 :=
  build_words n capacity positive frequency

theorem space (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat)
    (nonempty : 0 < capacity) : (build n capacity positive frequency).words ≤ 10 * n * capacity :=
  build_space n capacity positive frequency nonempty

/-- The cursor advances by stored links, ending at the requested key's local root. -/
theorem query (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat) (p x : Fin n) :
    LinkedSearch.Request (build n capacity positive frequency) p x x
      (LinkedSearch.request (build n capacity positive frequency) p x).2 :=
  request_execution n capacity positive frequency p x

/-- Worst-case query cost includes a possible failed cache search and fallback. -/
theorem uniform (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat)
    (nonempty : 0 < capacity) (p x : Fin n) :
    ((LinkedSearch.request (build n capacity positive frequency) p x).2 : ℝ) ≤
      Real.logb 2 (2 * ((min capacity n : Nat) : ℝ)) + Real.logb 2 (2 * (n : ℝ)) + 4 :=
  request_uniform n capacity positive frequency nonempty p x

/-- A normalized per-transition information bound, including capacity one. -/
theorem tradeoff (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat)
    (nonempty : 0 < capacity) (fits : capacity ≤ n) (p x : Fin n) (observed : 0 < frequency p x) :
    ((LinkedSearch.request (build n capacity positive frequency) p x).2 : ℝ) ≤
      6 * (1 + Real.logb 2 ((ConditionalEntropy.rowTotal n frequency p : ℝ) / frequency p x)) *
        (1 + Real.logb 2 n) / (1 + Real.logb 2 capacity) :=
  request_tradeoff n capacity positive frequency nonempty fits p x observed

/-- Theorem 9 of arXiv:1304.6897 in the explicit static linked-pointer model.
The empirical matrix is used for preprocessing only. Cost includes one unit
per visited node and each fallback/successor link traversal. Request normalization
and `1 + log` factors cover deterministic rows, empty sequences, and capacity one.
The initial predecessor is explicit; preprocessing time is not part of the bound. -/
theorem sequence (n capacity : Nat) (positive : 0 < n)
    (nonempty : 0 < capacity) (fits : capacity ≤ n) (p : Fin n) (xs : List (Fin n)) :
    ∃ q k,
      LinkedSearch.Execution (build n capacity positive (LazyFinger.frequency p (xs.map Fin.val)))
        p (xs.map Fin.val) q k ∧
      (k : ℝ) ≤ 6 * ConditionalEntropy.cost n p (xs.map Fin.val) *
        (1 + Real.logb 2 n) / (1 + Real.logb 2 capacity) ∧
      (build n capacity positive (LazyFinger.frequency p (xs.map Fin.val))).words ≤ 10 * n * capacity :=
  sequence_tradeoff n capacity positive nonempty fits p xs

/-- For each fixed positive exponent, Section 7's structure uses
`O(n^(1+ε))` words and `O(m(1+H))` query work. The integer capacity is chosen
before the sequence; preprocessing the actual trees still uses its empirical
frequencies. The constants are explicit, including exponents greater than one.
Initialization uses the specified predecessor and preprocessing time is excluded. -/
theorem polynomial_space (n : Nat) (positive : 0 < n) (ε : ℝ) (exponent : 0 < ε) :
    ∃ capacity : Nat, 0 < capacity ∧ capacity ≤ n ∧
      ∀ (p : Fin n) (xs : List (Fin n)), ∃ q k,
        LinkedSearch.Execution
          (build n capacity positive (LazyFinger.frequency p (xs.map Fin.val)))
          p (xs.map Fin.val) q k ∧
        (k : ℝ) ≤ (6 / min ε 1) * (xs.length : ℝ) *
          (1 + ConditionalEntropy.entropy n p (xs.map Fin.val)) ∧
        ((build n capacity positive (LazyFinger.frequency p (xs.map Fin.val))).words : ℝ) ≤
          20 * (n : ℝ) ^ (1 + ε) :=
  MultipleTrees.polynomial_space n positive ε exponent

end RotationBST.MultipleTrees.Results

/-- info: abstract audit passed for `RotationBST.MultipleTrees.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.MultipleTrees.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Labelled.Search.Definitions.Abstract,
  RotationBST.Models.LinkedSearch.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Frequencies.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Edges.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Bounds.ConditionalEntropy.Definitions.Abstract,
  RotationBST.Structures.WeightedSearch.Definitions.Abstract,
  RotationBST.Algorithms.MultipleTrees.Selection.Definitions.Abstract,
  RotationBST.Algorithms.MultipleTrees.Cache.Definitions.Abstract,
  RotationBST.Algorithms.MultipleTrees.Definitions.Abstract]
