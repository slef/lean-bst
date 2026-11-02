module

public import RotationBST.Model.Rotations

@[expose] public section

/-! Constructive rotation connectivity. Adapted from `TreeReset.lean` on
`origin/state-elimination` (5f0159d), checked independently in this library. -/
namespace RotationBST

variable {s t : Tree} {x k : Nat}

def spine : Nat → Tree → Tree
  | 0, t => t
  | n + 1, t => .node .nil (spine n t)

theorem spine_add (n m : Nat) (t : Tree) : spine (n + m) t = spine n (spine m t) := by
  induction n with
  | zero => simp [spine]
  | succ n ih => simp [spine, Nat.succ_add, ih]

theorem Rotations.inSpine (h : Rotations s t k) (n : Nat) :
    Rotations (spine n s) (spine n t) k := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.inRight

/-- Empty the root's left subtree into a right spine, using exactly its size
in rotations. The right subtree is kept as a continuation. -/
theorem promote_left (l r : Tree) :
    Rotations (.node l r) (spine l.size (.node .nil r)) l.size := by
  induction l generalizing r with
  | nil => exact .refl
  | node a b ia ib =>
      have first : Rotations (.node (.node a b) r)
          (spine a.size (.node .nil (.node b r))) (a.size + 1) :=
        .step .right (ia (.node b r))
      have second := ((ib r).inRight (l := Tree.nil)).inSpine a.size
      have result := first.append second
      simpa only [Tree.size, spine_add, spine, Nat.add_assoc] using result

/-- Convert a tree to the canonical right vine with at most n rotations. -/
theorem to_spine (t : Tree) : ∃ k, k ≤ t.size ∧ Rotations t (spine t.size .nil) k := by
  induction t with
  | nil => exact ⟨0, Nat.le_refl _, .refl⟩
  | node l r _ ir =>
      obtain ⟨k, hk, hr⟩ := ir
      have first := promote_left l r
      have second := (hr.inRight (l := Tree.nil)).inSpine l.size
      refine ⟨l.size + k, ?_, ?_⟩
      · simp only [Tree.size]; omega
      · have result := first.append second
        simpa only [Tree.size, Nat.add_assoc, spine_add, spine] using result

theorem Rotate.symm (h : Rotate s t) : Rotate t s := by
  induction h with
  | right => exact .left
  | left => exact .right
  | inLeft _ ih => exact .inLeft ih
  | inRight _ ih => exact .inRight ih

theorem Rotations.symm (h : Rotations s t k) : Rotations t s k := by
  induction h with
  | refl => exact .refl
  | step hr _ ih => exact ih.append (.step hr.symm .refl)

/-- Any two shapes on the same key universe are at most `2n` rotations apart. -/
theorem reset_linear (s t : Tree) (h : s.size = t.size) :
    ∃ k, k ≤ 2 * s.size ∧ Rotations s t k := by
  obtain ⟨i, hi, hs⟩ := to_spine s
  obtain ⟨j, hj, ht⟩ := to_spine t
  rw [← h] at ht hj
  exact ⟨i + j, by omega, hs.append ht.symm⟩

/-- Charge a reset at the beginning of the next access so that the requested
key is still at the root when the access ends. -/
theorem reset_then_access (s t u : Tree) (hs : s.size = t.size)
    (ha : Access t u x k) :
    ∃ j, j ≤ 2 * s.size ∧ Access s u x (j + k) := by
  obtain ⟨j, hj, hr⟩ := reset_linear s t hs
  exact ⟨j, hj, hr.append ha.1, ha.2⟩

end RotationBST
