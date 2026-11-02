module

public import RotationBST.Pointer.Lazy.Skeleton.Abstract
public import RotationBST.Pointer.Reversal

@[expose] public section

namespace RotationBST.Pointer.Lazy.Skeleton

/-- Remaining work in the elementary vine construction. Each right rotation or
advance along the right spine decreases this measure by one. -/
def work : Skeleton → Nat
  | .hole _ => 0
  | .node l r => 2 * l.size + 1 + work r

theorem work_le (s : Skeleton) : s.work ≤ 2 * s.size := by
  induction s with
  | hole => simp [work, size]
  | node l r _ ih => simp only [work, size]; omega

theorem fringe_length (s : Skeleton) : s.fringe.length = s.size + 1 := by
  induction s with
  | hole => rfl
  | node l r il ir => simp [fringe, size, il, ir, Nat.add_assoc]

theorem fringe_ne_nil (s : Skeleton) : s.fringe ≠ [] := by
  have := fringe_length s
  intro h
  rw [h] at this
  simp at this

theorem vine_cons (a : Tree) (s : Skeleton) : vine (a :: s.fringe) = .node a (vine s.fringe) := by
  cases h : s.fringe with
  | nil => exact False.elim (s.fringe_ne_nil h)
  | cons b bs => rfl

theorem vine_node (l r : Skeleton) : ∃ a b, vine (Skeleton.node l r).fringe = .node a b := by
  have h := fringe_length (.node l r)
  cases hf : (Skeleton.node l r).fringe with
  | nil => simp [hf, size] at h
  | cons a rest =>
      cases rest with
      | nil => simp [hf, size] at h
      | cons b bs => exact ⟨a, vine (b :: bs), rfl⟩

/-- A connected region can be flattened in at most four pointer instructions per
active node, without entering or modifying any fringe subtree. -/
theorem flatten (s : Skeleton) :
    ∃ k, k ≤ 2 * s.work ∧ Pointer.Trace ⟨s.tree, []⟩ ⟨vine s.fringe, []⟩ k := by
  match s with
  | .hole t => exact ⟨0, by simp [work], .refl⟩
  | .node (.hole a) (.hole b) => exact ⟨0, by simp [work], .refl⟩
  | .node (.hole a) (.node b c) =>
      obtain ⟨k, hk, ht⟩ := flatten (.node b c)
      obtain ⟨u, v, huv⟩ := vine_node b c
      have hdown : Pointer.Trace ⟨.node a (.node b.tree c.tree), []⟩
          ⟨.node b.tree c.tree, [.right a]⟩ 1 := .step .downRight .refl
      have hmid := ht.under [.right a]
      have hup : Pointer.Trace ⟨.node u v, [.right a]⟩ ⟨.node a (.node u v), []⟩ 1 :=
        .step .upRight .refl
      simp only [Pointer.Config.under, List.nil_append, tree] at hmid
      rw [huv] at hmid
      refine ⟨1 + k + 1, ?_, ?_⟩
      · simp only [work, size] at *; omega
      · have hh := (hdown.append hmid).append hup
        change Pointer.Trace ⟨.node a (.node b.tree c.tree), []⟩
          ⟨vine (a :: (Skeleton.node b c).fringe), []⟩ (1 + k + 1)
        rw [vine_cons, huv]
        exact hh
  | .node (.node a b) c =>
      obtain ⟨k, hk, ht⟩ := flatten (.node a (.node b c))
      have first : Pointer.Trace ⟨.node (.node a.tree b.tree) c.tree, []⟩
          ⟨.node a.tree (.node b.tree c.tree), []⟩ 2 :=
        .step .downLeft (.step .rotateLeftChild .refl)
      refine ⟨2 + k, ?_, ?_⟩
      · simp only [work, size] at *; omega
      · simpa only [tree, fringe, List.append_assoc] using first.append ht
termination_by s.work
decreasing_by all_goals simp only [work, size]; omega

/-- Reshape a connected region with fixed fringe in linear pointer cost. -/
theorem reshape (s t : Skeleton) (same : s.fringe = t.fringe) :
    ∃ k, k ≤ 16 * s.size ∧ Pointer.Trace ⟨s.tree, []⟩ ⟨t.tree, []⟩ k := by
  obtain ⟨i, hi, hs⟩ := flatten s
  obtain ⟨j, hj, ht⟩ := flatten t
  obtain ⟨q, hq, hr⟩ := ht.reverse
  have heq : s.size = t.size := by
    have h := congrArg List.length same
    rw [fringe_length, fringe_length] at h
    omega
  rw [← same] at hr
  have hsw := work_le s
  have htw := work_le t
  exact ⟨i + q, by omega, hs.append hr⟩

end RotationBST.Pointer.Lazy.Skeleton
