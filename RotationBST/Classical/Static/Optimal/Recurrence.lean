module

public import RotationBST.Classical.Static.Optimal.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section

/-! The interval recurrence is the optimum over all trees, and its largest
optimal root builds an optimal tree. -/
namespace RotationBST.Classical.Static.Optimal

theorem foldr_min_le_init (a : Nat) (l : List Nat) : l.foldr min a ≤ a := by
  induction l with
  | nil => exact le_rfl
  | cons x l ih => exact (min_le_right _ _).trans ih

theorem foldr_min_le_mem (a : Nat) (l : List Nat) (x : Nat) (hx : x ∈ l) : l.foldr min a ≤ x := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hx)

theorem foldr_min_mem (a : Nat) (l : List Nat) : l.foldr min a = a ∨ l.foldr min a ∈ l := by
  induction l with
  | nil => exact Or.inl rfl
  | cons y l ih =>
    simp only [List.foldr_cons, List.mem_cons]
    rcases Nat.le_total y (l.foldr min a) with h | h
    · exact Or.inr (Or.inl (min_eq_left h))
    · rw [min_eq_right h]
      rcases ih with ih | ih
      · exact Or.inl ih
      · exact Or.inr (Or.inr ih)

theorem cost_empty (W : Nat → Nat → Nat) {i j : Nat} (h : j ≤ i) : cost W i j = 0 := by
  rw [cost]; simp [show ¬ i < j by omega]

theorem cost_self (W : Nat → Nat → Nat) (i : Nat) : cost W i i = 0 := cost_empty W le_rfl

theorem cost_eq (W : Nat → Nat → Nat) {i j : Nat} (h : i < j) :
    cost W i j = W i j + ((List.finRange (j - i)).map fun r : Fin (j - i) =>
      cost W i (i + r) + cost W (i + r + 1) j).foldr min (cost W i i + cost W (i + 1) j) := by
  rw [cost]; simp [h]

theorem cost_le_candidate (W : Nat → Nat → Nat) {i j r : Nat} (hi : i ≤ r) (hj : r < j) :
    cost W i j ≤ candidate W i j r := by
  rw [cost_eq W (by omega), candidate, Nat.add_assoc]
  apply Nat.add_le_add_left
  apply foldr_min_le_mem
  refine List.mem_map.mpr ⟨⟨r - i, by omega⟩, List.mem_finRange _, ?_⟩
  simp only
  rw [show i + (r - i) = r by omega]

theorem exists_optimal (W : Nat → Nat → Nat) {i j : Nat} (h : i < j) :
    ∃ r, i ≤ r ∧ r < j ∧ candidate W i j r = cost W i j := by
  have e := cost_eq W h
  rcases foldr_min_mem (cost W i i + cost W (i + 1) j) ((List.finRange (j - i)).map fun r : Fin (j - i) =>
      cost W i (i + r) + cost W (i + r + 1) j) with hm | hm
  · exact ⟨i, le_rfl, h, by rw [candidate, e, hm, Nat.add_assoc]⟩
  · obtain ⟨r, _, hr⟩ := List.mem_map.mp hm
    exact ⟨i + r, by omega, by omega, by rw [candidate, e, ← hr, Nat.add_assoc]⟩

theorem root_spec (W : Nat → Nat → Nat) {i j : Nat} (h : i < j) :
    i ≤ root W i j ∧ root W i j < j ∧ candidate W i j (root W i j) = cost W i j ∧
      ∀ r, i ≤ r → r < j → candidate W i j r = cost W i j → r ≤ root W i j := by
  obtain ⟨r, hir, hrj, hr⟩ := exists_optimal W h
  have hP : (fun d => candidate W i j (i + d) = cost W i j) (r - i) := by
    simp only; rw [show i + (r - i) = r by omega]; exact hr
  have hle := Nat.findGreatest_le (P := fun d => candidate W i j (i + d) = cost W i j) (j - i - 1)
  refine ⟨Nat.le_add_right _ _, by unfold root; omega, ?_, ?_⟩
  · exact Nat.findGreatest_spec (P := fun d => candidate W i j (i + d) = cost W i j)
      (show r - i ≤ j - i - 1 by omega) hP
  · intro s his hsj hs
    have := Nat.le_findGreatest (P := fun d => candidate W i j (i + d) = cost W i j)
      (show s - i ≤ j - i - 1 by omega) (by rw [show i + (s - i) = s by omega]; exact hs)
    unfold root; omega

theorem tree_eq (W : Nat → Nat → Nat) {i j : Nat} (h : i < j) :
    tree W i j = .node (tree W i (root W i j)) (tree W (root W i j + 1) j) := by
  rw [tree]; simp [h]

theorem tree_empty (W : Nat → Nat → Nat) {i j : Nat} (h : j ≤ i) : tree W i j = .nil := by
  rw [tree]; simp [show ¬ i < j by omega]

theorem tree_spec (W : Nat → Nat → Nat) (len : Nat) :
    ∀ i j, j - i = len → (tree W i j).size = j - i ∧ treeCost W (tree W i j) i = cost W i j := by
  induction len using Nat.strong_induction_on with
  | ind len ih =>
    intro i j hlen
    by_cases h : i < j
    · obtain ⟨h1, h2, h3, _⟩ := root_spec W h
      have hl := ih (root W i j - i) (by omega) i (root W i j) rfl
      have hr := ih (j - (root W i j + 1)) (by omega) (root W i j + 1) j rfl
      rw [tree_eq W h]
      refine ⟨by simp only [Tree.size, hl.1, hr.1]; omega, ?_⟩
      simp only [treeCost, Tree.size, hl.1, hl.2, hr.1]
      rw [show i + (root W i j - i + 1 + (j - (root W i j + 1))) = j by omega,
        show i + (root W i j - i) + 1 = root W i j + 1 by omega, hr.2, ← h3, candidate]
    · rw [tree_empty W (by omega), cost_empty W (by omega)]
      simp [Tree.size, treeCost]; omega

theorem tree_size (W : Nat → Nat → Nat) (i j : Nat) : (tree W i j).size = j - i :=
  (tree_spec W (j - i) i j rfl).1

theorem tree_cost (W : Nat → Nat → Nat) (i j : Nat) : treeCost W (tree W i j) i = cost W i j :=
  (tree_spec W (j - i) i j rfl).2

theorem cost_le_treeCost (W : Nat → Nat → Nat) (t : Tree) :
    ∀ i j, t.size = j - i → cost W i j ≤ treeCost W t i := by
  induction t with
  | nil =>
    intro i j h
    simp only [Tree.size] at h
    rw [cost_empty W (by omega)]; exact Nat.zero_le _
  | node l r ihl ihr =>
    intro i j h
    simp only [Tree.size] at h
    have hc := cost_le_candidate W (i := i) (j := j) (r := i + l.size) (by omega) (by omega)
    have hl := ihl i (i + l.size) (by omega)
    have hr := ihr (i + l.size + 1) j (by omega)
    simp only [treeCost, Tree.size, candidate] at hc ⊢
    rw [show i + (l.size + 1 + r.size) = j by omega]
    omega

end RotationBST.Classical.Static.Optimal
