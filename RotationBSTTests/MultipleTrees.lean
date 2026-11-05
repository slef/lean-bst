module

public import RotationBST.Algorithms.MultipleTrees.Abstract
public import RotationBST.Models.Labelled.Search.Abstract
public import RotationBST.Models.LinkedSearch.Abstract
import Mathlib.Tactic
import all Init.Data.List.Sort.Basic

@[expose] public section
namespace RotationBST.Tests.MultipleTrees

private def sparse : LabelledTree Nat := .node (.node .nil 10 .nil) 30 (.node .nil 90 .nil)

-- The stored labels are sparse: a query is not silently treated as an inorder
-- rank. Misses between, below, and above stored keys all traverse nodes.
example : LabelledTree.lookup sparse 10 = (true, 2) := by decide
example : LabelledTree.lookup sparse 1 = (false, 2) := by decide
example : LabelledTree.lookup sparse 20 = (false, 2) := by decide
example : LabelledTree.lookup sparse 100 = (false, 2) := by decide
example : LabelledTree.Search sparse 20 false 2 := LabelledTree.Search.Results.execution sparse 20
example : ((Tree.node (.node .nil .nil) (.node .nil .nil)).labelWith [10, 30, 90]).inorder = [10, 30, 90] :=
  (LabelledTree.Search.Results.labelling _ _ (by decide)).2

-- A deliberately unrelated successor pointer must be returned from the node's
-- field, rather than recomputed from its key or the request.
private def linked : LabelledTree (LinkedSearch.Entry (Fin 4)) := .node .nil ⟨7, 2⟩ .nil
private def manual : LinkedSearch.Store (Fin 4) := ⟨fun _ => linked, .nil⟩
example : LinkedSearch.lookup linked 7 = (some 2, 1) := by decide
example : LinkedSearch.request manual 0 7 = (some 2, 2) := by decide
example : LinkedSearch.Request manual 0 7 2 2 :=
  LinkedSearch.Results.query manual 0 2 7 (by decide)

private def frequencies : Nat → Nat
  | 0 => 1
  | 1 => 7
  | 2 => 0
  | 3 => 7
  | _ => 0

private theorem selected_example : MultipleTrees.selected 4 2 frequencies = [1, 3] := by
  simp [MultipleTrees.selected, MultipleTrees.ranking, List.mergeSort,
    List.MergeSort.Internal.splitInTwo, List.splitAt_eq, frequencies, List.range_succ]

private theorem cache_keys : MultipleTrees.cacheKeys 4 2 frequencies = [1, 3] := by
  rw [MultipleTrees.cacheKeys, selected_example]
  simp

private theorem cache_shape : MultipleTrees.cacheTree 4 2 frequencies = .node (.node .nil 1 .nil) 3 .nil := by
  unfold MultipleTrees.cacheTree
  rw [cache_keys]
  decide

private theorem fallback_keys : MultipleTrees.cacheKeys 4 4 (fun _ => 0) = [0, 1, 2, 3] := by
  simp [MultipleTrees.cacheKeys, MultipleTrees.selected, MultipleTrees.ranking,
    List.mergeSort, List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.range_succ]

private theorem fallback_shape : MultipleTrees.fallbackTree 4 =
    .node (.node (.node .nil 0 .nil) 1 .nil) 2 (.node .nil 3 .nil) := by
  unfold MultipleTrees.fallbackTree MultipleTrees.cacheTree
  rw [fallback_keys]
  decide

private def fixture := MultipleTrees.build 4 2 (by decide) (fun _ => frequencies)

-- A local hit charges its search and stored link. An unobserved requested key
-- still succeeds through the fallback, after paying for the failed cache search.
private theorem hit_example : LinkedSearch.request fixture 0 3 = (some 3, 2) := by
  have result := MultipleTrees.request_hit 4 2 (by decide) (fun _ => frequencies) 0 3
    (by rw [selected_example]; decide)
  simpa [cache_shape, LabelledTree.lookup, fixture] using result

private theorem miss_example : LinkedSearch.request fixture 0 2 = (some 2, 5) := by
  have result := MultipleTrees.request_miss 4 2 (by decide) (fun _ => frequencies) 0 2
    (by rw [selected_example]; decide)
  simpa [cache_shape, fallback_shape, LabelledTree.lookup, fixture] using result

example : LinkedSearch.Request fixture 0 2 2 5 := by
  have trace := MultipleTrees.Results.query 4 2 (by decide) (fun _ => frequencies) 0 2
  change LinkedSearch.Request fixture 0 2 2 (LinkedSearch.request fixture 0 2).2 at trace
  simpa only [miss_example] using trace

example : fixture.nodes = 12 := MultipleTrees.Results.nodes 4 2 (by decide) (fun _ => frequencies)
example : fixture.words = 53 := MultipleTrees.Results.words 4 2 (by decide) (fun _ => frequencies)

-- Empty universes and oversized caches have the exact truncated sizes; entirely
-- unobserved rows retain valid comparison trees.
example : (MultipleTrees.cacheTree 0 4 frequencies).erase.size = 0 := MultipleTrees.Cache.Results.size 0 4 frequencies
example : (MultipleTrees.cacheTree 4 9 (fun _ => 0)).erase.size = 4 := MultipleTrees.Cache.Results.size 4 9 (fun _ => 0)
example : (MultipleTrees.cacheTree 4 1 (fun _ => 0)).Ordered := MultipleTrees.Cache.Results.ordered 4 1 (fun _ => 0)

-- The complete theorem includes empty sequences and capacity one without an
-- undefined log-base-one expression. A deterministic one-key sequence still
-- pays for its requests and successor links despite having zero information.
example : ∃ q k,
    LinkedSearch.Execution (MultipleTrees.build 1 1 (by decide) (LazyFinger.frequency 0 [])) 0 [] q k ∧
    (k : ℝ) ≤ 0 ∧
    (MultipleTrees.build 1 1 (by decide) (LazyFinger.frequency 0 [])).words ≤ 10 := by
  simpa [ConditionalEntropy.cost, ConditionalEntropy.sequenceInformation, ConditionalEntropy.information,
    LazyFinger.frequency] using MultipleTrees.Results.sequence 1 1 (by decide) (by decide) (by decide) 0 []

example : ∃ q k,
    LinkedSearch.Execution (MultipleTrees.build 1 1 (by decide) (LazyFinger.frequency 0 [0, 0, 0])) 0 [0, 0, 0] q k ∧
    (k : ℝ) ≤ 18 ∧
    (MultipleTrees.build 1 1 (by decide) (LazyFinger.frequency 0 [0, 0, 0])).words ≤ 10 := by
  have bound := MultipleTrees.Results.sequence 1 1 (by decide) (by decide) (by decide) 0 [0, 0, 0]
  norm_num [ConditionalEntropy.cost, ConditionalEntropy.sequenceInformation, ConditionalEntropy.information,
    ConditionalEntropy.rowTotal, LazyFinger.frequency] at bound ⊢
  exact bound

-- A fractional exponent on a universe that is not a perfect square still
-- gives one integer capacity for every sequence, with constant query overhead.
example : ∃ capacity : Nat, 0 < capacity ∧ capacity ≤ 3 ∧
    ∀ (p : Fin 3) (xs : List (Fin 3)), ∃ q k,
      LinkedSearch.Execution
        (MultipleTrees.build 3 capacity (by decide) (LazyFinger.frequency p (xs.map Fin.val)))
        p (xs.map Fin.val) q k ∧
      (k : ℝ) ≤ 12 * (xs.length : ℝ) *
        (1 + ConditionalEntropy.entropy 3 p (xs.map Fin.val)) ∧
      ((MultipleTrees.build 3 capacity (by decide)
        (LazyFinger.frequency p (xs.map Fin.val))).words : ℝ) ≤ 20 * (3 : ℝ) ^ (3 / 2 : ℝ) := by
  convert MultipleTrees.Results.polynomial_space 3 (by decide) (1 / 2) (by norm_num) using 1
  norm_num

-- Exponents above one saturate at full caches. For a singleton universe this
-- includes both an empty sequence and arbitrarily many deterministic requests.
example (xs : List (Fin 1)) : ∃ q k,
    LinkedSearch.Execution
      (MultipleTrees.build 1 1 (by decide) (LazyFinger.frequency 0 (xs.map Fin.val)))
      0 (xs.map Fin.val) q k ∧
    (k : ℝ) ≤ 6 * (xs.length : ℝ) *
      (1 + ConditionalEntropy.entropy 1 0 (xs.map Fin.val)) ∧
    ((MultipleTrees.build 1 1 (by decide) (LazyFinger.frequency 0 (xs.map Fin.val))).words : ℝ) ≤ 20 := by
  obtain ⟨capacity, nonempty, fits, bound⟩ :=
    MultipleTrees.Results.polynomial_space 1 (by decide) 2 (by norm_num)
  have single : capacity = 1 := by omega
  subst capacity
  simpa using bound 0 xs

/-- info: 'RotationBST.MultipleTrees.Results.polynomial_space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MultipleTrees.Results.polynomial_space

end RotationBST.Tests.MultipleTrees
