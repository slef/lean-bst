module

public import RotationBST.Algorithms.Tango.Algorithm.Balanced
public import RotationBST.Models.Online.Reset
public import RotationBST.Models.Rotation.Existence.Proofs

/-! Tango as an ordinary online algorithm (`RotationBST.Algorithm`). A policy
keeps marks on the edges of its tree; a plain algorithm sees only the tree and
the past requests. It needs no more: replaying the policy on the past requests
recomputes the marks. -/

@[expose] public section
namespace RotationBST.Tango
open MarkedTree

theorem Policy.runFrom_append_one {reference : Tree} (p : Policy reference)
    (past : List Nat) (s : MarkedTree) (ys : List Nat) (x : Nat) :
    p.runFrom past s (ys ++ [x]) =
      ((p.step (past ++ ys) (p.runFrom past s ys).1 x).1,
        (p.runFrom past s ys).2 + (p.step (past ++ ys) (p.runFrom past s ys).1 x).2) := by
  induction ys generalizing past s with
  | nil =>
    rcases h : p.step past s x with ⟨t, a⟩
    simp [Policy.runFrom, h]
  | cons y ys ih =>
    rcases h : p.step past s y with ⟨t, a⟩
    have rest := ih (past ++ [y]) t
    simp only [List.append_assoc, List.singleton_append] at rest
    simp only [List.cons_append, Policy.runFrom, h, rest]
    simp only [Prod.mk.injEq, true_and]
    omega

theorem Policy.run_append_one {reference : Tree} (p : Policy reference) (past : List Nat) (x : Nat) :
    (p.run (past ++ [x])).1 = (p.step past (p.run past).1 x).1 := by
  simp [Policy.run, Policy.runFrom_append_one]

/-- A Tango policy run as a plain online algorithm. The marks are recomputed by
replaying the policy on the past requests. A tree other than the policy's own,
which never occurs in a run from the reference tree, is served by splaying. -/
def Policy.toAlgorithm {reference : Tree} (p : Policy reference) : Algorithm where
  step past t x :=
    if (∀ y ∈ past, y < reference.size) ∧ x < reference.size ∧ t = (p.run past).1.tree then
      ((p.step past (p.run past).1 x).1.tree, (p.step past (p.run past).1 x).2)
    else Splay.run t x
  correct past t x valid := by
    by_cases h : (∀ y ∈ past, y < reference.size) ∧ x < reference.size ∧ t = (p.run past).1.tree
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      obtain ⟨history, hx, rfl⟩ := h
      exact (p.correct past (p.run past).1 x (p.run_spec past history).2.1 history hx).1
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
      exact (Splay.run_correct t x valid).1

theorem Policy.toAlgorithm_runFrom {reference : Tree} (p : Policy reference) (past xs : List Nat)
    (history : ∀ y ∈ past, y < reference.size) (valid : ∀ x ∈ xs, x < reference.size) :
    (p.toAlgorithm.runFrom past (p.run past).1.tree xs).2 = (p.runFrom past (p.run past).1 xs).2 := by
  induction xs generalizing past with
  | nil => simp [Algorithm.runFrom, Policy.runFrom]
  | cons x xs ih =>
    have hx : x < reference.size := valid x (by simp)
    have step : p.toAlgorithm.step past (p.run past).1.tree x =
        ((p.step past (p.run past).1 x).1.tree, (p.step past (p.run past).1 x).2) := by
      unfold Policy.toAlgorithm
      exact ite_eq_left_of_eq_true _ _ (eq_true ⟨history, hx, rfl⟩)
    have extended : ∀ y ∈ past ++ [x], y < reference.size := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact history y hy
      · rw [List.mem_singleton.mp hy]; exact hx
    have rest := ih (past ++ [x]) extended (fun y hy => valid y (by simp [hy]))
    rw [p.run_append_one] at rest
    simp only [Algorithm.runFrom, step, Policy.runFrom, rest]

/-- From the reference tree, the plain algorithm performs exactly the policy's rotations. -/
theorem Policy.toAlgorithm_cost {reference : Tree} (p : Policy reference) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < reference.size) :
    p.toAlgorithm.cost reference xs = (p.run xs).2 := by
  have h := p.toAlgorithm_runFrom [] xs (by simp) valid
  simpa [Algorithm.cost, Policy.run, Policy.runFrom, initial_tree] using h

/-- Tango from any initial tree: rotate into the balanced reference tree on the
first request, then run the policy. -/
theorem exists_online_bound (n : Nat) :
    ∃ A : Algorithm, ∀ {start finish : Tree} {xs : List Nat} {offline : Nat},
      start.size = n → Execution start xs finish offline →
        (A.totalCost start xs : ℝ) ≤
          (56 * Real.logb 2 (Nat.log2 n + 1) + 16) * (offline + xs.length : Nat) +
            (14 * Real.logb 2 (Nat.log2 n + 1) + 6) * n := by
  let p := policy (balanced n)
  refine ⟨resetAlgorithm p.toAlgorithm (balanced n), ?_⟩
  intro start finish xs offline size execution
  have same : start.size = (balanced n).size := size.trans (balanced_size n).symm
  have valid : ∀ x ∈ xs, x < (balanced n).size := by
    intro x hx; rw [← same]; exact AccessBridge.execution_valid execution x hx
  have reset := resetAlgorithm_cost p.toAlgorithm (balanced n) start same xs
  rw [p.toAlgorithm_cost xs valid, size] at reset
  have bound := p.balanced_competitive_bound n size execution
  have cast : ((resetAlgorithm p.toAlgorithm (balanced n)).cost start xs : ℝ) ≤ (p.run xs).2 + 2 * n := by
    exact_mod_cast reset
  have nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [Algorithm.totalCost, Nat.cast_add] at bound ⊢
  linarith

end RotationBST.Tango
