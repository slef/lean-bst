module

public import RotationBST.Structures.BSTDeque.Definitions.Abstract
public import RotationBST.Models.Pointer.Lazy.Skeleton

@[expose] public section

namespace RotationBST.BSTDeque

open Pointer.Lazy

@[simp] theorem frontSpine_size (xs : List Tree) (gap : Tree) :
    (frontSpine xs gap).size = xs.length := by
  induction xs with
  | nil => rfl
  | cons g gs ih => simp [frontSpine, Skeleton.size, ih, Nat.add_comm]

@[simp] theorem backSpine_size (xs : List Tree) (gap : Tree) :
    (backSpine xs gap).size = xs.length := by
  induction xs with
  | nil => rfl
  | cons g gs ih => simp [backSpine, Skeleton.size, ih]

@[simp] theorem frontSpine_fringe (xs : List Tree) (gap : Tree) :
    (frontSpine xs gap).fringe = xs ++ [gap] := by
  induction xs with
  | nil => rfl
  | cons g gs ih => simp [frontSpine, Skeleton.fringe, ih]

@[simp] theorem backSpine_fringe (xs : List Tree) (gap : Tree) :
    (backSpine xs gap).fringe = gap :: xs.reverse := by
  induction xs with
  | nil => rfl
  | cons g gs ih => simp [backSpine, Skeleton.fringe, ih]

namespace Deque

@[simp] theorem skeleton_size (q : Deque) : q.skeleton.size = q.size := by
  cases q <;> simp [skeleton, size, Skeleton.size]

@[simp] theorem skeleton_fringe (q : Deque) : q.skeleton.fringe = q.fringe := by
  cases q <;> simp [skeleton, fringe, Skeleton.fringe, List.append_assoc]

theorem fringe_length (q : Deque) : q.fringe.length = q.size + 1 := by
  simpa using Skeleton.fringe_length q.skeleton

theorem fringe_ne_nil (q : Deque) : q.fringe ≠ [] := by
  have := fringe_length q
  intro h
  simp [h] at this

theorem balance_fringe (xs : List Tree) (nonempty : xs ≠ []) :
    (balance xs).fringe = xs := by
  have len : 0 < xs.length := List.length_pos_iff.mpr nonempty
  have split := List.take_append_drop ((xs.length - 2) / 2) xs
  have dropLen : (xs.drop ((xs.length - 2) / 2)).length =
      xs.length - (xs.length - 2) / 2 := List.length_drop
  unfold balance
  dsimp only
  split
  next a b rest h =>
    simpa [h, fringe, List.append_assoc] using split
  next a h =>
    have short : xs.length = 1 := by rw [h] at dropLen; simp at dropLen; omega
    have eq : xs = [a] := by simpa [short] using h
    exact eq.symm
  next h =>
    rw [h] at dropLen
    simp at dropLen
    omega

theorem balance_potential (xs : List Tree) : (balance xs).potential ≤ 32 := by
  have dropLen : (xs.drop ((xs.length - 2) / 2)).length =
      xs.length - (xs.length - 2) / 2 := List.length_drop
  unfold balance
  dsimp only
  split
  next a b rest h =>
    rw [h] at dropLen
    simp only [List.length_cons] at dropLen
    simp only [potential, List.length_take, List.length_reverse, Nat.dist]
    omega
  all_goals simp [potential]

theorem balance_size (xs : List Tree) (nonempty : xs ≠ []) :
    (balance xs).size + 1 = xs.length := by
  rw [← fringe_length, balance_fringe xs nonempty]

@[simp] theorem pushFront_fringe (g : Tree) (q : Deque) :
    (q.pushFront g).fringe = g :: q.fringe := by
  cases q <;> simp [pushFront, fringe]

@[simp] theorem pushBack_fringe (g : Tree) (q : Deque) :
    (q.pushBack g).fringe = q.fringe ++ [g] := by
  cases q <;> simp [pushBack, fringe, List.append_assoc]

@[simp] theorem pushFront_size (g : Tree) (q : Deque) :
    (q.pushFront g).size = q.size + 1 := by
  cases q <;> simp [pushFront, size]; omega

@[simp] theorem pushBack_size (g : Tree) (q : Deque) :
    (q.pushBack g).size = q.size + 1 := by
  cases q <;> simp [pushBack, size]; omega

theorem popFront_fringe {q r : Deque} {g : Tree} (h : q.popFront = some (g, r)) :
    q.fringe = g :: r.fringe := by
  cases q with
  | empty a => simp [popFront] at h
  | node front a b back =>
    cases front with
    | nil =>
      simp only [popFront, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rw [balance_fringe _ (by simp)]
      rfl
    | cons x xs =>
      simp only [popFront, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl

theorem popBack_fringe {q r : Deque} {g : Tree} (h : q.popBack = some (g, r)) :
    q.fringe = r.fringe ++ [g] := by
  cases q with
  | empty a => simp [popBack] at h
  | node front a b back =>
    cases back with
    | nil =>
      simp only [popBack, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rw [balance_fringe _ (by simp)]
      simp [fringe, List.append_assoc]
    | cons x xs =>
      simp only [popBack, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp [fringe, List.append_assoc]

theorem popFront_size {q r : Deque} {g : Tree} (h : q.popFront = some (g, r)) :
    q.size = r.size + 1 := by
  have := congrArg List.length (popFront_fringe h)
  simp only [List.length_cons, fringe_length] at this
  omega

theorem popBack_size {q r : Deque} {g : Tree} (h : q.popBack = some (g, r)) :
    q.size = r.size + 1 := by
  have := congrArg List.length (popBack_fringe h)
  simp only [List.length_append, List.length_singleton, fringe_length] at this
  omega

end Deque
end RotationBST.BSTDeque
