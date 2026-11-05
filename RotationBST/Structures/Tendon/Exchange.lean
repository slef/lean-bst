module

public import RotationBST.Structures.Tendon.Representation

@[expose] public section
namespace RotationBST.Tendon

open Pointer.Lazy

/-- Reassociate one external upper key through the lower deque's short boundary
path, without entering the rest of either deque. -/
theorem lower_exchange (q : BSTDeque.Deque) (a b : Tree) :
    (∃ k, k ≤ 48 ∧ Pointer.Trace ⟨.node (Pointer.plug q.maxContext a) b, []⟩
      ⟨Pointer.plug q.maxContext (.node a b), []⟩ k) ∧
    (∃ k, k ≤ 48 ∧ Pointer.Trace ⟨Pointer.plug q.maxContext (.node a b), []⟩
      ⟨.node (Pointer.plug q.maxContext a) b, []⟩ k) := by
  let s := Skeleton.node ((Skeleton.hole a).under q.maxContext) (.hole b)
  let t := (Skeleton.node (.hole a) (.hole b)).under q.maxContext
  have same : s.fringe = t.fringe := by
    simp [s, t, Skeleton.fringe, path_fringe, maxContext_upper, List.append_assoc]
  have sizeS : s.size ≤ 3 := by
    have := q.maxContext_length
    simp only [s, Skeleton.size, Skeleton.under_size]
    omega
  have sizeT : t.size ≤ 3 := by
    have := q.maxContext_length
    simp only [t, Skeleton.under_size, Skeleton.size]
    omega
  obtain ⟨i, hi, first⟩ := Skeleton.reshape s t same
  obtain ⟨j, hj, second⟩ := Skeleton.reshape t s same.symm
  constructor
  · refine ⟨i, by omega, ?_⟩
    simpa only [s, t, Skeleton.tree, Skeleton.under_tree] using first
  · refine ⟨j, by omega, ?_⟩
    simpa only [s, t, Skeleton.tree, Skeleton.under_tree] using second

/-- The symmetric reassociation through the upper deque's minimum-side path. -/
theorem upper_exchange (q : BSTDeque.Deque) (a b : Tree) :
    (∃ k, k ≤ 48 ∧ Pointer.Trace ⟨.node a (Pointer.plug q.minContext b), []⟩
      ⟨Pointer.plug q.minContext (.node a b), []⟩ k) ∧
    (∃ k, k ≤ 48 ∧ Pointer.Trace ⟨Pointer.plug q.minContext (.node a b), []⟩
      ⟨.node a (Pointer.plug q.minContext b), []⟩ k) := by
  let s := Skeleton.node (.hole a) ((Skeleton.hole b).under q.minContext)
  let t := (Skeleton.node (.hole a) (.hole b)).under q.minContext
  have same : s.fringe = t.fringe := by
    simp [s, t, Skeleton.fringe, path_fringe, minContext_lower]
  have sizeS : s.size ≤ 3 := by
    have := q.minContext_length
    simp only [s, Skeleton.size, Skeleton.under_size]
    omega
  have sizeT : t.size ≤ 3 := by
    have := q.minContext_length
    simp only [t, Skeleton.under_size, Skeleton.size]
    omega
  obtain ⟨i, hi, first⟩ := Skeleton.reshape s t same
  obtain ⟨j, hj, second⟩ := Skeleton.reshape t s same.symm
  constructor
  · refine ⟨i, by omega, ?_⟩
    simpa only [s, t, Skeleton.tree, Skeleton.under_tree] using first
  · refine ⟨j, by omega, ?_⟩
    simpa only [s, t, Skeleton.tree, Skeleton.under_tree] using second

end RotationBST.Tendon
