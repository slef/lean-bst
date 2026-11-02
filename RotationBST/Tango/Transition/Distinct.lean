module

public import RotationBST.Tango.Transition.Intervals
import Mathlib.Data.List.Nodup

@[expose] public section
namespace RotationBST.Tango

theorem transitionKeys_bounds (reference : Tree) (lo : Nat) (actual : Tree) (x : Nat)
    (h : x ∈ transitionKeys reference lo actual) : lo ≤ x ∧ x < lo + reference.size := by
  induction reference generalizing lo with
  | nil => simp [transitionKeys] at h
  | node l r il ir =>
    simp only [transitionKeys, List.mem_append, Option.mem_toList] at h
    rcases h with (h | h) | h
    · have hb := transition_bounds (by omega) (by omega) h
      simpa only [Tree.size, Nat.add_assoc] using hb
    · have := il lo h
      simp only [Tree.size]; omega
    · have := ir (lo + l.size + 1) h
      simp only [Tree.size]; omega

/-- The top key of any containing interval cannot be a transition key of a
reference cut inside that interval. -/
theorem transitionKeys_exclude_top (reference : Tree) (lo : Nat) (actual : Tree)
    (low high root : Nat) (lower : low ≤ lo) (upper : lo + reference.size ≤ high)
    (top : topIn actual 0 low high = some root) : root ∉ transitionKeys reference lo actual := by
  induction reference generalizing lo with
  | nil => simp [transitionKeys]
  | node l r il ir =>
    intro h
    simp only [transitionKeys, List.mem_append, Option.mem_toList] at h
    rcases h with (h | h) | h
    · have hb := transition_bounds (by omega) (by omega) h
      have nested := topIn_nested actual 0 low high lo (lo + l.size + 1 + r.size) root top
        lower (by simp only [Tree.size] at upper; omega) hb.1 hb.2
      exact transition_ne_top nested h rfl
    · exact il lo lower (by simp only [Tree.size] at upper; omega) h
    · exact ir (lo + l.size + 1) (by omega) (by simp only [Tree.size] at upper; omega) h

private theorem root_excludes_children (l r actual : Tree) (lo point : Nat)
    (h : transition actual lo (lo + l.size) (lo + l.size + 1 + r.size) = some point) :
    point ∉ transitionKeys l lo actual ∧ point ∉ transitionKeys r (lo + l.size + 1) actual := by
  unfold transition at h
  split at h
  · contradiction
  · split at h
    · have hb := topIn_bounds h
      constructor
      · intro hp
        have := transitionKeys_bounds l lo actual point hp
        omega
      · exact transitionKeys_exclude_top r (lo + l.size + 1) actual
          (lo + l.size + 1) (lo + l.size + 1 + r.size) point le_rfl le_rfl h
    · have hb := topIn_bounds h
      constructor
      · exact transitionKeys_exclude_top l lo actual lo (lo + l.size + 1) point
          le_rfl (by omega) h
      · intro hp
        have := transitionKeys_bounds r (lo + l.size + 1) actual point hp
        omega

/-- Different reference cuts have different transition points in the current
BST. This is the injectivity needed to charge Wilber switches to touches. -/
theorem transitionKeys_nodup (reference : Tree) (lo : Nat) (actual : Tree) :
    (transitionKeys reference lo actual).Nodup := by
  induction reference generalizing lo with
  | nil => simp [transitionKeys]
  | node l r il ir =>
    have dis : List.Disjoint (transitionKeys l lo actual) (transitionKeys r (lo + l.size + 1) actual) := by
      intro x hl hr
      have := transitionKeys_bounds l lo actual x hl
      have := transitionKeys_bounds r (lo + l.size + 1) actual x hr
      omega
    have child := List.nodup_append.mpr ⟨il lo, ir (lo + l.size + 1),
      fun a ha b hb he => dis ha (he.symm ▸ hb)⟩
    simp only [transitionKeys]
    cases he : transition actual lo (lo + l.size) (lo + l.size + 1 + r.size) with
    | none => simpa using child
    | some point =>
      have hn := root_excludes_children l r actual lo point he
      change (point :: (transitionKeys l lo actual ++ transitionKeys r (lo + l.size + 1) actual)).Nodup
      exact List.nodup_cons.mpr ⟨fun hp => (List.mem_append.mp hp).elim hn.1 hn.2, child⟩

end RotationBST.Tango
