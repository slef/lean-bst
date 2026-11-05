module

public import RotationBST.Structures.BSTDeque.Shape

@[expose] public section

namespace RotationBST.BSTDeque.Deque

open Pointer.Lazy

theorem pushFront_potential (g : Tree) (q : Deque) :
    (q.pushFront g).potential ≤ q.potential + 32 := by
  cases q <;> simp only [pushFront, potential, List.length_cons, List.length_nil, Nat.dist]
  all_goals omega

theorem pushBack_potential (g : Tree) (q : Deque) :
    (q.pushBack g).potential ≤ q.potential + 32 := by
  cases q <;> simp only [pushBack, potential, List.length_cons, List.length_nil, Nat.dist]
  all_goals omega

/-- Insert a supplied parent into the minimum stack in at most two pointer
instructions. The cursor starts and finishes at the whole tree's root. -/
theorem pushFront_trace (g : Tree) (q : Deque) :
    ∃ k, k ≤ 2 ∧ Pointer.Trace ⟨.node g q.tree, []⟩ ⟨(q.pushFront g).tree, []⟩ k := by
  cases q with
  | empty a => exact ⟨0, by omega, .refl⟩
  | node front a b back =>
    exact ⟨2, by omega, .step .downRight (.step .rotateRightChild .refl)⟩

theorem pushBack_trace (g : Tree) (q : Deque) :
    ∃ k, k ≤ 2 ∧ Pointer.Trace ⟨.node q.tree g, []⟩ ⟨(q.pushBack g).tree, []⟩ k := by
  cases q with
  | empty a => exact ⟨0, by omega, .refl⟩
  | node front a b back =>
    exact ⟨2, by omega, .step .downLeft (.step .rotateLeftChild .refl)⟩

/-- Pop exposes the minimum as a parent, preserving the complete tree. Emptying
a stack triggers a linear reshaping, paid for by the old imbalance. -/
theorem popFront_trace {q r : Deque} {g : Tree} (h : q.popFront = some (g, r)) :
    ∃ k, k + r.potential ≤ 80 + q.potential ∧
      Pointer.Trace ⟨q.tree, []⟩ ⟨.node g r.tree, []⟩ k := by
  cases q with
  | empty a => simp [popFront] at h
  | node front a b back =>
    cases front with
    | nil =>
      simp only [popFront, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      let q : Deque := .node [] a b back
      let r := balance (b :: back.reverse)
      have same : q.skeleton.fringe = (Skeleton.node (.hole a) r.skeleton).fringe := by
        rw [skeleton_fringe, Skeleton.fringe, Skeleton.fringe, skeleton_fringe]
        exact popFront_fringe (q := q) (r := r) rfl
      obtain ⟨k, bound, trace⟩ := Skeleton.reshape _ _ same
      have pot := balance_potential (b :: back.reverse)
      refine ⟨k, ?_, trace⟩
      simp only [skeleton_size, q, size, List.length_nil] at bound
      change k + (balance (b :: back.reverse)).potential ≤
        80 + 32 * Nat.dist 0 back.length
      simp only [Nat.dist]
      omega
    | cons x xs =>
      simp only [popFront, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨2, ?_, .step .downLeft (.step .rotateLeftChild .refl)⟩
      simp only [potential, List.length_cons, Nat.dist]
      omega

theorem popBack_trace {q r : Deque} {g : Tree} (h : q.popBack = some (g, r)) :
    ∃ k, k + r.potential ≤ 80 + q.potential ∧
      Pointer.Trace ⟨q.tree, []⟩ ⟨.node r.tree g, []⟩ k := by
  cases q with
  | empty a => simp [popBack] at h
  | node front a b back =>
    cases back with
    | nil =>
      simp only [popBack, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      let q : Deque := .node front a b []
      let r := balance (front ++ [a])
      have same : q.skeleton.fringe = (Skeleton.node r.skeleton (.hole b)).fringe := by
        rw [skeleton_fringe, Skeleton.fringe, Skeleton.fringe, skeleton_fringe]
        exact popBack_fringe (q := q) (r := r) rfl
      obtain ⟨k, bound, trace⟩ := Skeleton.reshape _ _ same
      have pot := balance_potential (front ++ [a])
      refine ⟨k, ?_, trace⟩
      simp only [skeleton_size, q, size, List.length_nil] at bound
      change k + (balance (front ++ [a])).potential ≤
        80 + 32 * Nat.dist front.length 0
      simp only [Nat.dist]
      omega
    | cons x xs =>
      simp only [popBack, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨2, ?_, .step .downRight (.step .rotateRightChild .refl)⟩
      simp only [potential, List.length_cons, Nat.dist]
      omega

end RotationBST.BSTDeque.Deque
