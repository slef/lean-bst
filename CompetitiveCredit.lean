import CostComposition

/-! The least competitive credit for a fixed tree-only algorithm already known
to be offline competitive. These lemmas do not supply such an algorithm. -/
namespace RotationBST

private theorem least_nat {p : Nat → Prop} (h : ∃ n, p n) :
    ∃ n, p n ∧ ∀ m, p m → n ≤ m := by
  classical
  obtain ⟨n, hn⟩ := h
  have aux : ∀ n, p n → ∃ k, p k ∧ ∀ m, p m → k ≤ m := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro hp
        by_cases hs : ∃ m, m < n ∧ p m
        · obtain ⟨m, hm, hpm⟩ := hs
          exact ih m hm hpm
        · refine ⟨n, hp, ?_⟩
          intro m hm
          apply Classical.byContradiction
          intro hnot
          exact hs ⟨m, by omega, hm⟩
  exact aux n hn

def CreditBound (b : TreeAlgorithm) (C : Nat) (s t : Tree) (d : Nat) : Prop :=
  ∀ xs u k, Execution t xs u k → b.totalCost s xs ≤ C * (xs.length + k) + d

def OfflineCompetitiveWith (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat) : Prop :=
  ∀ t, CreditBound b C t t (f t.size)

theorem credit_exists (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (h : OfflineCompetitiveWith b C f) (s t : Tree) (hs : s.size = t.size) :
    ∃ d, CreditBound b C s t d ∧ ∀ e, CreditBound b C s t e → d ≤ e := by
  apply least_nat
  exact ⟨f s.size + C * (2 * s.size), fun xs u k he =>
    competitive_change_start b C f h s t hs he⟩

noncomputable def credit (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (h : OfflineCompetitiveWith b C f) (s t : Tree) : Nat :=
  if hs : s.size = t.size then Classical.choose (credit_exists b C f h s t hs) else 0

theorem credit_spec (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (h : OfflineCompetitiveWith b C f) (s t : Tree) (hs : s.size = t.size) :
    CreditBound b C s t (credit b C f h s t) := by
  rw [credit, dif_pos hs]
  exact (Classical.choose_spec (credit_exists b C f h s t hs)).1

theorem credit_le (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (h : OfflineCompetitiveWith b C f) (s t : Tree) (hs : s.size = t.size)
    (hd : CreditBound b C s t d) : credit b C f h s t ≤ d := by
  rw [credit, dif_pos hs]
  exact (Classical.choose_spec (credit_exists b C f h s t hs)).2 d hd

/-- Integer-valued bounded excess attains its largest value on a finite word. -/
theorem credit_attained (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (h : OfflineCompetitiveWith b C f) (s t : Tree) (hs : s.size = t.size) :
    ∃ xs u k, Execution t xs u k ∧
      b.totalCost s xs = C * (xs.length + k) + credit b C f h s t := by
  classical
  by_cases hz : credit b C f h s t = 0
  · exact ⟨[], t, 0, .nil, by simp [StatefulAlgorithm.totalCost, StatefulAlgorithm.runFrom, hz]⟩
  · apply Classical.byContradiction
    intro hnone
    have smaller : CreditBound b C s t (credit b C f h s t - 1) := by
      intro xs u k he
      have hb := credit_spec b C f h s t hs xs u k he
      have hn : b.totalCost s xs ≠ C * (xs.length + k) + credit b C f h s t := by
        intro eq
        exact hnone ⟨xs, u, k, he, eq⟩
      omega
    have hm := credit_le b C f h s t hs smaller
    omega

/-- At an endpoint attaining the maximum excess, every continuation has
nonpositive excess. Thus some equal-size starting pair needs zero credit. -/
theorem zero_credit_pair (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (h : OfflineCompetitiveWith b C f) (t : Tree) :
    ∃ s u, s.size = t.size ∧ u.size = t.size ∧ credit b C f h s u = 0 := by
  obtain ⟨xs, u, k, he, htight⟩ := credit_attained b C f h t t rfl
  let s := (b.runFrom () t xs).2.1
  have hs : t.size = s.size := (b.execution () t xs he.validInput).size_eq
  have hu : t.size = u.size := he.size_eq
  have zero_bound : CreditBound b C s u 0 := by
    intro ys v m hy
    have hb := credit_spec b C f h t t rfl (xs ++ ys) v (k + m) (he.append hy)
    rw [treeOnly_cost_append] at hb
    change b.totalCost t xs + b.totalCost s ys ≤ _ at hb
    rw [htight] at hb
    simp only [List.length_append, Nat.mul_add] at hb ⊢
    omega
  have hc := credit_le b C f h s u (by omega) zero_bound
  exact ⟨s, u, hs.symm, hu.symm, by omega⟩

/-- Changing the offline starting tree changes the required credit by at most
C times a linear reset cost. -/
theorem credit_lipschitz (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (h : OfflineCompetitiveWith b C f) (s t u : Tree)
    (hst : s.size = t.size) (hsu : s.size = u.size) :
    credit b C f h s t ≤ credit b C f h s u + C * (2 * s.size) := by
  apply credit_le b C f h s t hst
  intro xs v k he
  by_cases hempty : xs = []
  · subst xs; simp [StatefulAlgorithm.totalCost, StatefulAlgorithm.runFrom]
  · obtain ⟨j, hj, hr⟩ := reset_linear u t (by omega)
    have hb := credit_spec b C f h s u hsu xs v (j + k) (he.prepend_rotations hr hempty)
    rw [← hsu] at hj
    have hm := Nat.mul_le_mul_left C hj
    simp only [Nat.mul_add] at *
    omega

theorem credit_step (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (h : OfflineCompetitiveWith b C f) (s t u : Tree)
    (hst : s.size = t.size) (ha : Access t u x k) :
    1 + (b.step () s x).2.2 + credit b C f h (b.step () s x).2.1 u ≤
      C * (1 + k) + credit b C f h s t := by
  have hx : x < s.size := by rw [hst]; exact ha.in_range
  have hb := b.correct () s x hx
  have hs' : (b.step () s x).2.1.size = u.size := by
    rw [← hb.1.size_eq, hst, ha.1.size_eq]
  obtain ⟨ys, v, m, he, htight⟩ := credit_attained b C f h (b.step () s x).2.1 u hs'
  have hfull := credit_spec b C f h s t hst (x :: ys) v (k + m) (.cons ha he)
  rw [treeOnly_cost_cons, htight] at hfull
  simp only [List.length_cons, Nat.mul_add] at hfull ⊢
  omega

/-- info: 'RotationBST.zero_credit_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_credit_pair

end RotationBST
