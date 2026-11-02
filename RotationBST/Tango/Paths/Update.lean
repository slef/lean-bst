module

public import RotationBST.Tango.Paths.Bounds

@[expose] public section
namespace RotationBST.Tango

private theorem rest_mem_parts (d : PathDecomposition) {p : List Nat} (h : p ∈ d.2) : p ∈ d.parts := by
  unfold PathDecomposition.parts
  split
  · exact h
  · exact List.mem_cons_of_mem _ h

private theorem decompose_nonempty (reference : Tree) (lo : Nat) (past : List Nat) :
    ∀ p ∈ (decomposePaths reference lo past).parts, p ≠ [] := by
  induction reference generalizing lo with
  | nil => simp [decomposePaths, PathDecomposition.parts]
  | node l r il ir =>
    have lp := il lo
    have rp := ir (lo + l.size + 1)
    have lr : ∀ p ∈ (decomposePaths l lo past).2, p ≠ [] :=
      fun p hp => lp p (rest_mem_parts _ hp)
    have rr : ∀ p ∈ (decomposePaths r (lo + l.size + 1) past).2, p ≠ [] :=
      fun p hp => rp p (rest_mem_parts _ hp)
    cases h : (labels lo (lo + l.size) (lo + l.size + 1 + r.size) past).getLast?
    all_goals try cases ‹Bool›
    all_goals
      simp only [decomposePaths, h, PathDecomposition.parts, List.cons_ne_nil, ite_false]
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simp
      · rcases List.mem_append.mp hp with hp | hp
        · first | exact lp p hp | exact lr p hp
        · first | exact rp p hp | exact rr p hp

theorem preferredPaths_nonempty (reference : Tree) (past : List Nat) :
    ∀ path ∈ preferredPaths reference past, path ≠ [] := decompose_nonempty reference 0 past

/-- After updating preferences for a request, that key lies on the component
starting at the reference root. This is the component Tango finally searches. -/
theorem request_on_root_path (reference : Tree) (lo : Nat) (past : List Nat) (x : Nat)
    (lower : lo ≤ x) (upper : x < lo + reference.size) :
    x ∈ (decomposePaths reference lo (past ++ [x])).1 := by
  induction reference generalizing lo with
  | nil => simp only [Tree.size] at upper; omega
  | node l r il ir =>
    have hhi : x < lo + l.size + 1 + r.size := by simp only [Tree.size] at upper; omega
    have last : (labels lo (lo + l.size) (lo + l.size + 1 + r.size) (past ++ [x])).getLast? =
        some (decide (x ≤ lo + l.size)) := by
      simp [labels, lower, hhi]
    simp only [decomposePaths, last]
    by_cases left : x < lo + l.size
    · have side : x ≤ lo + l.size := by omega
      simp only [decide_eq_true side]
      exact List.mem_cons_of_mem _ (il lo lower left)
    · by_cases root : x = lo + l.size
      · subst x
        simp
      · have side : ¬ x ≤ lo + l.size := by omega
        simp only [decide_eq_false side]
        exact List.mem_cons_of_mem _ (ir (lo + l.size + 1) (by omega) (by omega))

end RotationBST.Tango
