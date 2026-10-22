import CostComposition

/-! Prefixes of a finite-horizon optimal execution lose at most one reset
against an independently optimal prefix. This supports a compactness route
to a serving plan for a known infinite request sequence. -/
namespace RotationBST

def RotationOptimal (t : Tree) (xs : List Nat) (k : Nat) : Prop :=
  ∀ u j, Execution t xs u j → k ≤ j

private theorem least_nat (p : Nat → Prop) (h : ∃ n, p n) :
    ∃ k, p k ∧ ∀ m, p m → k ≤ m := by
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

theorem optimal_execution_exists (t : Tree) (xs : List Nat) (hv : ValidInput t xs) :
    ∃ u k, Execution t xs u k ∧ RotationOptimal t xs k := by
  have he := moveToRootAlgorithm.execution () t xs hv
  obtain ⟨k,⟨u,hu⟩,hk⟩ := least_nat (fun k => ∃ u, Execution t xs u k) ⟨_,_,he⟩
  exact ⟨u,k,hu,fun v j hj => hk j ⟨v,hj⟩⟩

/-- Replacing an optimal execution's prefix and resetting before its suffix
shows that every prefix is within 2n rotations of any alternative prefix. -/
theorem optimal_prefix_bound (hpre : Execution t xs s k)
    (hsuf : Execution s ys u m) (opt : RotationOptimal t (xs ++ ys) (k+m))
    (alternative : Execution t xs v j) : k ≤ j + 2*t.size := by
  by_cases he : ys = []
  · subst ys
    cases hsuf
    have hb := opt v j (by simpa using alternative)
    omega
  · have hsize : v.size = s.size := alternative.size_eq.symm.trans hpre.size_eq
    obtain ⟨r,hr,hreset⟩ := reset_linear v s hsize
    have hs := hsuf.prepend_rotations hreset he
    have hc := opt u (j+(r+m)) (alternative.append hs)
    have hv := alternative.size_eq
    rw [← hv] at hr
    omega

/-- An optimal prefix comparison can use a different initial tree of equal
size, paying one additional reset. -/
theorem optimal_prefix_other_start (hpre : Execution t xs s k)
    (hsuf : Execution s ys u m) (opt : RotationOptimal t (xs ++ ys) (k+m))
    (alternative : Execution v xs z j) (hsize : t.size = v.size) :
    k ≤ j + 4*t.size := by
  by_cases he : xs = []
  · subst xs; cases hpre; omega
  · obtain ⟨r,hr,hreset⟩ := reset_linear t v hsize
    have hb := optimal_prefix_bound hpre hsuf opt (alternative.prepend_rotations hreset he)
    omega

/-- Each action in an optimal finite plan has at most 2n rotations: replace
it by a shortest-reset upper bound while preserving its requested-root endpoint. -/
theorem optimal_access_bound (hpre : Execution t pre s j)
    (ha : Access s v x k) (hsuf : Execution v tail u m)
    (opt : RotationOptimal t (pre ++ x::tail) (j+(k+m))) :
    k ≤ 2*t.size := by
  obtain ⟨r,hr,hh⟩ := reset_linear s v ha.1.size_eq
  have replacement : Access s v x r := ⟨hh,ha.2⟩
  have hc := opt u (j+(r+m)) (hpre.append (.cons replacement hsuf))
  have hsize := hpre.size_eq
  rw [← hsize] at hr
  omega

/-- info: 'RotationBST.optimal_prefix_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms optimal_prefix_bound
end RotationBST
