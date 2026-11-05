module

public import RotationBST.Algorithms.MultipleTrees.Construction
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.MultipleTrees

/-- Exact hit cost, including following the stored successor-root pointer. -/
theorem request_hit (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat)
    (p x : Fin n) (stored : x.val ∈ selected n capacity (frequency p)) :
    LinkedSearch.request (build n capacity positive frequency) p x =
      (some x, (LabelledTree.lookup (cacheTree n capacity (frequency p)) x).2 + 1) := by
  have hit := (cacheTree_lookup n capacity (frequency p) x).mpr stored
  simp only [LinkedSearch.request, build, LinkedSearch.attach_lookup, hit, ↓reduceIte,
    rootAddress_valid n positive x x.isLt, Fin.eta]

/-- Exact miss cost includes both searches, the fallback jump, and the stored
successor-root link obtained at the end of the fallback search. -/
theorem request_miss (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat)
    (p x : Fin n) (omitted : x.val ∉ selected n capacity (frequency p)) :
    LinkedSearch.request (build n capacity positive frequency) p x =
      (some x, (LabelledTree.lookup (cacheTree n capacity (frequency p)) x).2 +
        (LabelledTree.lookup (fallbackTree n) x).2 + 2) := by
  have miss : (LabelledTree.lookup (cacheTree n capacity (frequency p)) x).1 = false := by
    cases h : (LabelledTree.lookup (cacheTree n capacity (frequency p)) x).1
    · rfl
    · exact False.elim (omitted ((cacheTree_lookup n capacity (frequency p) x).mp h))
  have fallback := (fallbackTree_lookup n x).mpr x.isLt
  simp only [LinkedSearch.request, build, LinkedSearch.attach_lookup, miss, fallback, Bool.false_eq_true, ↓reduceIte,
    rootAddress_valid n positive x x.isLt, Fin.eta]

/-- Every valid request succeeds and leaves the cursor at the requested key's
local-root cell. The next query can use that pointer directly. -/
theorem request_success (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat)
    (p x : Fin n) : (LinkedSearch.request (build n capacity positive frequency) p x).1 = some x := by
  by_cases stored : x.val ∈ selected n capacity (frequency p)
  · rw [request_hit n capacity positive frequency p x stored]
  · rw [request_miss n capacity positive frequency p x stored]

theorem request_execution (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat)
    (p x : Fin n) : LinkedSearch.Request (build n capacity positive frequency) p x x
      (LinkedSearch.request (build n capacity positive frequency) p x).2 :=
  LinkedSearch.request_correct _ p x x (request_success n capacity positive frequency p x)

/-- A cache hit costs the biased search bound plus its successor-link traversal. -/
theorem request_hit_weighted (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat)
    (p x : Fin n) (stored : x.val ∈ selected n capacity (frequency p)) (observed : 0 < frequency p x) :
    ((LinkedSearch.request (build n capacity positive frequency) p x).2 : ℝ) ≤
      Real.logb 2 (3 * (((List.range n).map (frequency p)).sum : ℝ) / frequency p x) + 2 := by
  rw [request_hit n capacity positive frequency p x stored, Nat.cast_add, Nat.cast_one]
  have bound := cacheTree_weighted n capacity (frequency p) x stored observed
  linarith

/-- All requests have logarithmic worst-case cost, including unobserved rows
and cache misses. This is the two-search bound before the entropy tradeoff. -/
theorem request_uniform (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat)
    (nonempty : 0 < capacity) (p x : Fin n) :
    ((LinkedSearch.request (build n capacity positive frequency) p x).2 : ℝ) ≤
      Real.logb 2 (2 * ((min capacity n : Nat) : ℝ)) + Real.logb 2 (2 * (n : ℝ)) + 4 := by
  have cacheBound := cacheTree_uniform n capacity (frequency p) x (Nat.lt_min.mpr ⟨nonempty, positive⟩)
  have fallbackBound := cacheTree_uniform n n (fun _ => 0) x (by simpa using positive)
  simp only [Nat.min_self] at fallbackBound
  change ((LabelledTree.lookup (fallbackTree n) x).2 : ℝ) ≤ _ at fallbackBound
  have logNonnegative : 0 ≤ Real.logb 2 (2 * (n : ℝ)) := by
    apply Real.logb_nonneg (by norm_num)
    have : (1 : ℝ) ≤ n := by exact_mod_cast positive
    linarith
  by_cases stored : x.val ∈ selected n capacity (frequency p)
  · rw [request_hit n capacity positive frequency p x stored, Nat.cast_add, Nat.cast_one]
    linarith
  · rw [request_miss n capacity positive frequency p x stored, Nat.cast_add, Nat.cast_add, Nat.cast_ofNat]
    linarith

end RotationBST.MultipleTrees
