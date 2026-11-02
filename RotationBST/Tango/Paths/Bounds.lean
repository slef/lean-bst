module

public import RotationBST.Tango.Paths.Partition

@[expose] public section
namespace RotationBST.Tango

private theorem parts_bound (d : PathDecomposition) (n : Nat)
    (head : d.1.length ≤ n) (rest : ∀ p ∈ d.2, p.length ≤ n) :
    ∀ p ∈ d.parts, p.length ≤ n := by
  unfold PathDecomposition.parts
  split
  · exact rest
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact head
    · exact rest p hp

private theorem decomposition_bound (reference : Tree) (lo : Nat) (past : List Nat) :
    (decomposePaths reference lo past).1.length ≤ height reference ∧
      ∀ p ∈ (decomposePaths reference lo past).2, p.length ≤ height reference := by
  induction reference generalizing lo with
  | nil => simp [decomposePaths, height]
  | node l r il ir =>
    obtain ⟨lh, lr⟩ := il lo
    obtain ⟨rh, rr⟩ := ir (lo + l.size + 1)
    have lp := parts_bound (decomposePaths l lo past) (height l) lh lr
    have rp := parts_bound (decomposePaths r (lo + l.size + 1) past) (height r) rh rr
    have hl : height l ≤ height (.node l r) := by simp only [height]; omega
    have hr : height r ≤ height (.node l r) := by simp only [height]; omega
    have lr' : ∀ p ∈ (decomposePaths l lo past).2, p.length ≤ height (.node l r) :=
      fun p hp => Nat.le_trans (lr p hp) hl
    have rr' : ∀ p ∈ (decomposePaths r (lo + l.size + 1) past).2, p.length ≤ height (.node l r) :=
      fun p hp => Nat.le_trans (rr p hp) hr
    have lp' : ∀ p ∈ (decomposePaths l lo past).parts, p.length ≤ height (.node l r) :=
      fun p hp => Nat.le_trans (lp p hp) hl
    have rp' : ∀ p ∈ (decomposePaths r (lo + l.size + 1) past).parts, p.length ≤ height (.node l r) :=
      fun p hp => Nat.le_trans (rp p hp) hr
    cases h : (labels lo (lo + l.size) (lo + l.size + 1 + r.size) past).getLast?
    all_goals try cases ‹Bool›
    all_goals
      simp only [decomposePaths, h]
      constructor
      · simp only [List.length_cons, List.length_nil, height]; omega
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · first | exact lp' p hp | exact lr' p hp
        · first | exact rp' p hp | exact rr' p hp

theorem preferredPaths_size (reference : Tree) (past : List Nat) :
    ∀ path ∈ preferredPaths reference past, path.length ≤ height reference := by
  obtain ⟨head, rest⟩ := decomposition_bound reference 0 past
  exact parts_bound _ _ head rest

end RotationBST.Tango
