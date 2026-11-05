module

public import RotationBST.Models.Labelled.Search.Correctness
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LabelledTree

/-- Searching a sparse key at inorder rank `i` visits exactly one plus the
ordinary rank depth of the underlying shape. No unit-cost rank lookup is used
by the search: the executable algorithm compares the actual stored labels. -/
theorem lookup_rank_cost (t : Tree) (keys : List Nat) (same : keys.length = t.size)
    (ordered : keys.Pairwise (· < ·)) (i : Nat) (valid : i < keys.length) :
    (lookup (t.labelWith keys) keys[i]).2 = Tree.depth t i + 1 := by
  induction t generalizing keys i with
  | nil => simp only [Tree.size] at same; omega
  | node l r il ir =>
    have rootValid : l.size < keys.length := by simp only [Tree.size] at same; omega
    have leftLength : (keys.take l.size).length = l.size := by simp only [List.length_take]; omega
    have rightLength : (keys.drop (l.size + 1)).length = r.size := by
      simp only [List.length_drop, Tree.size] at *; omega
    by_cases left : i < l.size
    · have childValid : i < (keys.take l.size).length := by rw [leftLength]; exact left
      have compared := ordered.rel_getElem_of_lt valid rootValid left
      have recurse := il (keys.take l.size) leftLength ordered.take i childValid
      simp only [List.getElem_take] at recurse
      simp only [Tree.labelWith, lookup, List.getElem?_eq_getElem rootValid, Option.getD_some,
        compared, ↓reduceIte, Tree.depth, left, recurse]
    · by_cases root : i = l.size
      · subst i
        simp only [Tree.labelWith, lookup, List.getElem?_eq_getElem rootValid, Option.getD_some,
          Nat.lt_irrefl, ↓reduceIte, Tree.depth, Nat.zero_add]
      · have right : l.size < i := by omega
        have compared := ordered.rel_getElem_of_lt rootValid valid right
        have childValid : i - l.size - 1 < (keys.drop (l.size + 1)).length := by
          simp only [List.length_drop]; omega
        have recurse := ir (keys.drop (l.size + 1)) rightLength ordered.drop _ childValid
        have position : l.size + 1 + (i - l.size - 1) = i := by omega
        simp only [List.getElem_drop, position] at recurse
        simp only [Tree.labelWith, lookup, List.getElem?_eq_getElem rootValid, Option.getD_some,
          Nat.not_lt.mpr (Nat.le_of_lt compared), Nat.ne_of_gt compared, ↓reduceIte,
          Tree.depth, left, root, recurse]

/-- Any search, successful or not, visits no more nodes than a root-to-key
path in the same tree. This turns all-key depth bounds into miss-cost bounds. -/
theorem lookup_cost_witness (t : LabelledTree Nat) (x : Nat) :
    (lookup t x).2 = 0 ∨ ∃ i < t.erase.size,
      (lookup t x).2 ≤ Tree.depth t.erase i + 1 := by
  induction t with
  | nil => exact Or.inl rfl
  | node l key r il ir =>
    have rootValid : l.erase.size < (LabelledTree.node l key r).erase.size := by
      simp only [erase, Tree.size]; omega
    by_cases low : x < key
    · rcases il with zero | ⟨i, valid, bound⟩
      · refine Or.inr ⟨l.erase.size, rootValid, ?_⟩
        simp [lookup, low, zero, erase, Tree.depth]
      · refine Or.inr ⟨i, by simp only [erase, Tree.size]; omega, ?_⟩
        simp only [lookup, low, ↓reduceIte, erase, Tree.depth, valid]
        omega
    · by_cases equal : x = key
      · refine Or.inr ⟨l.erase.size, rootValid, ?_⟩
        simp [lookup, equal, erase, Tree.depth]
      · rcases ir with zero | ⟨i, valid, bound⟩
        · refine Or.inr ⟨l.erase.size, rootValid, ?_⟩
          simp [lookup, low, equal, zero, erase, Tree.depth]
        · refine Or.inr ⟨l.erase.size + 1 + i, by simp only [erase, Tree.size]; omega, ?_⟩
          have high : ¬ l.erase.size + 1 + i < l.erase.size := by omega
          have notRoot : l.erase.size + 1 + i ≠ l.erase.size := by omega
          have position : l.erase.size + 1 + i - l.erase.size - 1 = i := by omega
          simp only [lookup, low, equal, ↓reduceIte, erase, Tree.depth, high, notRoot, position]
          omega

/-- A uniform depth bound controls successful and unsuccessful sparse searches. -/
theorem lookup_cost_le (t : LabelledTree Nat) (x : Nat) (D : ℝ) (nonnegative : 0 ≤ D)
    (depths : ∀ i < t.erase.size, (Tree.depth t.erase i : ℝ) ≤ D) :
    ((lookup t x).2 : ℝ) ≤ D + 1 := by
  rcases lookup_cost_witness t x with zero | ⟨i, valid, bound⟩
  · rw [zero]
    norm_num
    linarith
  · have path := depths i valid
    have cast : ((lookup t x).2 : ℝ) ≤ (Tree.depth t.erase i : ℝ) + 1 := by exact_mod_cast bound
    linarith

end RotationBST.LabelledTree
