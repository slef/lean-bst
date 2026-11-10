module

public import RotationBST.Classical.Random.Definitions.Abstract
public import RotationBST.Classical.Random.Depth
public import RotationBST.Structures.Treap.Order.Abstract
public import RotationBST.Structures.Treap.Random.Support
import Mathlib.Tactic

@[expose] public section

/-! Inserting keys without rebalancing builds the treap of the insertion
order: the first key is the root, and the others split by comparison. -/
namespace RotationBST.Classical.Random
open Treap.Random

theorem insertKey_size (t : LabelledTree Nat) (y : Nat) :
    (insertKey t y).erase.size = t.erase.size + 1 := by
  induction t with
  | nil => simp [insertKey, LabelledTree.erase, Tree.size]
  | node l x r il ir =>
    simp only [insertKey]; split
    · simp only [LabelledTree.erase, Tree.size, il]; omega
    · simp only [LabelledTree.erase, Tree.size, ir]; omega

theorem insertAll_size (order : List Nat) : (insertAll order).erase.size = order.length := by
  unfold insertAll
  suffices ∀ t : LabelledTree Nat, (order.foldl insertKey t).erase.size = t.erase.size + order.length by
    simpa [LabelledTree.erase, Tree.size] using this .nil
  induction order with
  | nil => simp
  | cons y ys ih => intro t; simp only [List.foldl_cons, ih, insertKey_size, List.length_cons]; omega

/-- Later keys pass the root `x` on the side given by comparison. -/
theorem foldl_node (x : Nat) (rest : List Nat) (hx : x ∉ rest) (l r : LabelledTree Nat) :
    rest.foldl insertKey (.node l x r) =
      .node ((rest.filter (· < x)).foldl insertKey l) x ((rest.filter fun y => ¬ y < x).foldl insertKey r) := by
  induction rest generalizing l r with
  | nil => rfl
  | cons y ys ih =>
    have hy : y ≠ x := fun h => hx (h ▸ List.mem_cons_self ..)
    have hx' : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    simp only [List.foldl_cons, insertKey]
    by_cases h : y < x
    · simp only [h, ↓reduceIte]
      rw [List.filter_cons_of_pos (by simp [h]), List.filter_cons_of_neg (by simp [h]),
        List.foldl_cons, ih hx']
    · simp only [h, ↓reduceIte]
      rw [List.filter_cons_of_neg (by simp [h]), List.filter_cons_of_pos (by simp [h]),
        List.foldl_cons, ih hx']

theorem insertAll_cons (x : Nat) (rest : List Nat) (hx : x ∉ rest) :
    insertAll (x :: rest) =
      .node (insertAll (rest.filter (· < x))) x (insertAll (rest.filter fun y => ¬ y < x)) := by
  simp only [insertAll, List.foldl_cons, insertKey]
  exact foldl_node x rest hx .nil .nil

/-- In a list without repetitions, a sublist's first key comes first. -/
theorem idxOf_lt_of_sublist {L : List Nat} (hL : L.Nodup) {x : Nat} {rest : List Nat}
    (hs : (x :: rest).Sublist L) {y : Nat} (hy : y ∈ rest) : L.idxOf x < L.idxOf y := by
  induction L with
  | nil => simp at hs
  | cons a L ih =>
    obtain ⟨ha, hL'⟩ := List.nodup_cons.mp hL
    cases hs with
    | cons _ hs' =>
      have hxL : x ∈ L := hs'.subset (List.mem_cons_self ..)
      have hyL : y ∈ L := hs'.subset (List.mem_cons_of_mem _ hy)
      rw [List.idxOf_cons_ne _ (by rintro rfl; exact ha hxL), List.idxOf_cons_ne _ (by rintro rfl; exact ha hyL)]
      exact Nat.succ_lt_succ (ih hL' hs')
    | cons_cons _ hs' =>
      have hyL : y ∈ L := hs'.subset hy
      rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (by rintro rfl; exact ha hyL)]
      exact Nat.succ_pos _

theorem filter_range'_lt (lo k x : Nat) (h : lo ≤ x) (h' : x ≤ lo + k) :
    (List.range' lo k).filter (· < x) = List.range' lo (x - lo) := by
  induction k generalizing lo with
  | zero => have : x = lo := by omega
            subst this; simp
  | succ k ih =>
    rw [List.range'_succ, List.filter_cons]
    by_cases hx : lo = x
    · subst hx
      simp only [lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.sub_self, List.range'_zero]
      rw [List.filter_eq_nil_iff]; intro a ha; simp [List.mem_range'] at ha; simp; omega
    · simp only [show lo < x by omega, decide_true, ↓reduceIte]
      rw [ih (lo + 1) (by omega) (by omega), show x - lo = (x - (lo + 1)) + 1 by omega, List.range'_succ]

theorem filter_range'_ge (lo k x : Nat) (h : lo ≤ x) (h' : x ≤ lo + k) :
    (List.range' lo k).filter (fun y => ¬ y < x) = List.range' x (lo + k - x) := by
  induction k generalizing lo with
  | zero => have : x = lo := by omega
            subst this; simp
  | succ k ih =>
    rw [List.range'_succ, List.filter_cons]
    by_cases hx : lo = x
    · subst hx
      simp only [lt_irrefl, not_false_eq_true, decide_true, ↓reduceIte]
      rw [show lo + (k + 1) - lo = k + 1 by omega, List.range'_succ]
      congr 1
      rw [List.filter_eq_self]; intro a ha; simp [List.mem_range'] at ha; simp; omega
    · simp only [show lo < x by omega, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [ih (lo + 1) (by omega) (by omega), show lo + 1 + k = lo + (k + 1) by omega]

/-- Every sublist of the insertion order holding an interval of keys builds a
treap for the order's positions. -/
theorem insertAll_heap {L : List Nat} (hL : L.Nodup) (k : Nat) :
    ∀ (M : List Nat) (lo : Nat), M.length = k → M.Sublist L → M.Perm (List.range' lo k) →
      Geometric.Heap L.idxOf (insertAll M).erase lo := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
  intro M lo hlen hsub hperm
  cases M with
  | nil => simp [insertAll, LabelledTree.erase, Geometric.Heap]
  | cons x rest =>
    have hnd : (x :: rest).Nodup := hperm.nodup_iff.mpr List.nodup_range'
    have hx : x ∉ rest := (List.nodup_cons.mp hnd).1
    have hxmem : x ∈ List.range' lo k := hperm.subset (List.mem_cons_self ..)
    rw [List.mem_range'_1] at hxmem
    have hA : (rest.filter (· < x)).Perm (List.range' lo (x - lo)) := by
      have := hperm.filter (· < x)
      rw [filter_range'_lt lo k x hxmem.1 (by omega)] at this
      simpa using this
    have hB : (rest.filter fun y => ¬ y < x).Perm (List.range' (x + 1) (lo + k - x - 1)) := by
      have := hperm.filter (fun y => ¬ y < x)
      rw [filter_range'_ge lo k x hxmem.1 (by omega),
        show lo + k - x = (lo + k - x - 1) + 1 by omega, List.range'_succ] at this
      simp only [List.filter_cons, lt_irrefl, not_false_eq_true, decide_true, ↓reduceIte] at this
      exact (List.perm_cons x).mp this
    have lA := hA.length_eq; have lB := hB.length_eq
    simp only [List.length_range'] at lA lB
    have hsA : (rest.filter (· < x)).Sublist L :=
      (List.filter_sublist).trans ((List.sublist_cons_self x rest).trans hsub)
    have hsB : (rest.filter fun y => ¬ y < x).Sublist L :=
      (List.filter_sublist).trans ((List.sublist_cons_self x rest).trans hsub)
    rw [insertAll_cons x rest hx]
    simp only [LabelledTree.erase, Geometric.Heap, insertAll_size, lA]
    simp only [List.length_cons] at hlen
    refine ⟨?_, ih _ (by omega) _ lo lA hsA hA, ?_⟩
    · intro z hz
      rw [show lo + (x - lo) = x by omega]
      by_cases hzx : lo + z = x
      · rw [hzx]
      · have hzm : lo + z ∈ x :: rest := hperm.symm.subset (by rw [List.mem_range'_1]; omega)
        have hzr : lo + z ∈ rest := by
          rcases List.mem_cons.mp hzm with h | h
          · exact absurd h hzx
          · exact h
        exact (idxOf_lt_of_sublist hL hsub hzr).le
    · rw [show lo + (x - lo) + 1 = x + 1 by omega]
      exact ih _ (by omega) _ (x + 1) lB hsB hB

/-- **Insertion builds the treap of the insertion order.** -/
theorem insertAll_treap (n : Nat) (order : List Nat) (h : order.Perm (List.range n)) :
    (insertAll order).erase.size = n ∧ Geometric.Heap order.idxOf (insertAll order).erase 0 := by
  have hlen : order.length = n := by simpa using h.length_eq
  refine ⟨by rw [insertAll_size, hlen], ?_⟩
  exact insertAll_heap (h.nodup_iff.mpr List.nodup_range) n order 0 hlen (List.Sublist.refl _)
    (by rw [List.range_eq_range'] at h; exact h)

/-! ### Random insertion orders -/

/-- A uniformly random order of the `n` keys is a permutation of them. -/
theorem perm_of_isOrder (n : Nat) (xs : List Nat) (h : IsOrder (Finset.range n) xs) :
    xs.Perm (List.range n) :=
  List.perm_of_nodup_nodup_toFinset_eq h.1 List.nodup_range (by rw [h.2, List.toFinset_range])

/-- The treap used for orders that are not permutations, where the value does
not matter. -/
noncomputable def treapOf (n : Nat) (xs : List Nat) : Tree :=
  if xs.Perm (List.range n) then (insertAll xs).erase
  else (Geometric.TreapOrder.Results.exists_tree xs.idxOf n 0).choose

theorem treapOf_spec (n : Nat) (xs : List Nat) :
    (treapOf n xs).size = n ∧ Geometric.Heap xs.idxOf (treapOf n xs) 0 := by
  unfold treapOf
  split
  · exact insertAll_treap n xs (by assumption)
  · exact (Geometric.TreapOrder.Results.exists_tree xs.idxOf n 0).choose_spec

/-- **Random binary search trees.** Inserting the keys in a uniformly random
order, the expected depth of key `x` is `H(x + 1) + H(n - x) - 2`. -/
theorem random_bst_depth (n x : Nat) (hx : x < n) :
    average (fun _ => 1) (Finset.range n) (fun xs => ((insertAll xs).erase.depth x : ℝ)) =
      ((harmonic (x + 1) : ℚ) : ℝ) + ((harmonic (n - x) : ℚ) : ℝ) - 2 := by
  rw [← expected_depth n x hx (treapOf n) (treapOf_spec n)]
  have hw : ∀ k ∈ Finset.range n, (0 : ℝ) < 1 := fun _ _ => one_pos
  have heq : ∀ xs, IsOrder (Finset.range n) xs →
      ((insertAll xs).erase.depth x : ℝ) = ((treapOf n xs).depth x : ℝ) := by
    intro xs hxs
    simp [treapOf, perm_of_isOrder n xs hxs]
  exact le_antisymm (average_mono _ _ _ _ hw fun xs h => (heq xs h).le)
    (average_mono _ _ _ _ hw fun xs h => (heq xs h).ge)

theorem random_bst_depth_le (n x : Nat) (hx : x < n) :
    average (fun _ => 1) (Finset.range n) (fun xs => ((insertAll xs).erase.depth x : ℝ)) ≤
      2 * Real.log n := by
  rw [random_bst_depth n x hx, ← expected_depth n x hx (treapOf n) (treapOf_spec n)]
  exact expected_depth_le n x hx (treapOf n) (treapOf_spec n)

end RotationBST.Classical.Random
