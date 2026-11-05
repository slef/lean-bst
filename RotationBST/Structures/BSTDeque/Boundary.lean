module

public import RotationBST.Structures.BSTDeque.Boundary.Definitions.Abstract
public import RotationBST.Structures.BSTDeque.Shape
public import RotationBST.Models.Pointer.Lazy.Skeleton.Boundary
public import RotationBST.Models.Pointer.Navigation

@[expose] public section
namespace RotationBST.BSTDeque.Deque

open Pointer.Lazy

theorem fringe_minGap (q : Deque) : q.fringe = q.minGap :: q.fringe.tail := by
  cases q with
  | empty => rfl
  | node front a b back => cases front <;> rfl

theorem fringe_maxGap (q : Deque) : q.fringe = q.fringe.dropLast ++ [q.maxGap] := by
  cases q with
  | empty => rfl
  | node front a b back =>
    cases back <;> simp [fringe, maxGap, List.append_assoc]
    simp only [← List.cons_append, List.dropLast_concat]

@[simp] theorem withMin_fringe (q : Deque) (g : Tree) :
    (q.withMin g).fringe = g :: q.fringe.tail := by
  cases q with
  | empty => rfl
  | node front a b back => cases front <;> rfl

@[simp] theorem withMax_fringe (q : Deque) (g : Tree) :
    (q.withMax g).fringe = q.fringe.dropLast ++ [g] := by
  cases q with
  | empty => rfl
  | node front a b back =>
    cases back <;> simp [withMax, fringe, List.append_assoc]
    simp only [← List.cons_append, List.dropLast_concat]

@[simp] theorem withMin_context (q : Deque) (g : Tree) :
    (q.withMin g).minContext = q.minContext := by
  cases q with
  | empty => rfl
  | node front a b back => cases front <;> rfl

@[simp] theorem withMax_context (q : Deque) (g : Tree) :
    (q.withMax g).maxContext = q.maxContext := by
  cases q with
  | empty => rfl
  | node front a b back => cases back <;> rfl

@[simp] theorem withMin_potential (q : Deque) (g : Tree) :
    (q.withMin g).potential = q.potential := by
  cases q with
  | empty => rfl
  | node front a b back => cases front <;> rfl

@[simp] theorem withMax_potential (q : Deque) (g : Tree) :
    (q.withMax g).potential = q.potential := by
  cases q with
  | empty => rfl
  | node front a b back => cases back <;> rfl

theorem withMin_tree (q : Deque) (g : Tree) :
    (q.withMin g).tree = Pointer.plug q.minContext g := by
  cases q with
  | empty => rfl
  | node front a b back => cases front <;> rfl

theorem withMax_tree (q : Deque) (g : Tree) :
    (q.withMax g).tree = Pointer.plug q.maxContext g := by
  cases q with
  | empty => rfl
  | node front a b back => cases back <;> rfl

theorem minContext_tree (q : Deque) : Pointer.plug q.minContext q.minGap = q.tree := by
  cases q with
  | empty => rfl
  | node front a b back => cases front <;> rfl

theorem maxContext_tree (q : Deque) : Pointer.plug q.maxContext q.maxGap = q.tree := by
  cases q with
  | empty => rfl
  | node front a b back => cases back <;> rfl

@[simp] theorem withMin_size (q : Deque) (g : Tree) : (q.withMin g).size = q.size := by
  cases q with
  | empty => rfl
  | node front a b back => cases front <;> rfl

@[simp] theorem withMax_size (q : Deque) (g : Tree) : (q.withMax g).size = q.size := by
  cases q with
  | empty => rfl
  | node front a b back => cases back <;> rfl

theorem tree_of_fringe_min {q : Deque} {g : Tree} {xs : List Tree}
    (h : q.fringe = g :: xs) : q.tree = Pointer.plug q.minContext g := by
  have hg := q.fringe_minGap
  rw [h] at hg
  have eq : q.minGap = g := (List.cons.inj hg).1.symm
  rw [← eq]
  exact q.minContext_tree.symm

theorem tree_of_fringe_max {q : Deque} {g : Tree} {xs : List Tree}
    (h : q.fringe = xs ++ [g]) : q.tree = Pointer.plug q.maxContext g := by
  have hp : q.fringe.dropLast = xs := by simp [h]
  have hg := q.fringe_maxGap
  rw [hp, h] at hg
  have eq : q.maxGap = g := by simpa using (List.append_cancel_left hg).symm
  rw [← eq]
  exact q.maxContext_tree.symm

theorem popFront_exists (q : Deque) (positive : 0 < q.size) :
    ∃ g r, q.popFront = some (g, r) := by
  cases q with
  | empty => simp [size] at positive
  | node front a b back => cases front <;> exact ⟨_, _, rfl⟩

theorem popBack_exists (q : Deque) (positive : 0 < q.size) :
    ∃ g r, q.popBack = some (g, r) := by
  cases q with
  | empty => simp [size] at positive
  | node front a b back => cases back <;> exact ⟨_, _, rfl⟩

theorem minContext_length (q : Deque) : q.minContext.length ≤ 2 := by
  cases q with
  | empty => simp [minContext]
  | node front a b back => cases front <;> simp [minContext]

theorem maxContext_length (q : Deque) : q.maxContext.length ≤ 2 := by
  cases q with
  | empty => simp [maxContext]
  | node front a b back => cases back <;> simp [maxContext]

theorem minContext_fill (q : Deque) (s : Skeleton) :
    Pointer.plug q.minContext s.tree = (q.skeleton.fillMin s).tree := by
  cases q with
  | empty => rfl
  | node front a b back => cases front <;> rfl

theorem maxContext_fill (q : Deque) (s : Skeleton) :
    Pointer.plug q.maxContext s.tree = (q.skeleton.fillMax s).tree := by
  cases q with
  | empty => rfl
  | node front a b back => cases back <;> rfl

theorem minContext_offset (q : Deque) : Pointer.offset q.minContext = 0 := by
  cases q with
  | empty => rfl
  | node front a b back => cases front <;> rfl

theorem maxContext_offset (q : Deque) :
    Pointer.offset q.maxContext = q.size + (q.fringe.dropLast.map Tree.size).sum := by
  have front_size (xs : List Tree) (a : Tree) :
      (frontSpine xs a).tree.size = xs.length + (xs.map Tree.size).sum + a.size := by
    induction xs with
    | nil => simp [frontSpine, Skeleton.tree]
    | cons g gs ih => simp [frontSpine, Skeleton.tree, Tree.size, ih]; omega
  have back_size (xs : List Tree) (a : Tree) :
      (backSpine xs a).tree.size = xs.length + (xs.map Tree.size).sum + a.size := by
    induction xs with
    | nil => simp [backSpine, Skeleton.tree]
    | cons g gs ih => simp [backSpine, Skeleton.tree, Tree.size, ih]; omega
  cases q with
  | empty => simp [maxContext, Pointer.offset, size, fringe]
  | node front a b back =>
    cases back with
    | nil =>
      simp [maxContext, Pointer.offset, size, fringe, front_size]
      omega
    | cons g gs =>
      simp [maxContext, Pointer.offset, size, fringe, front_size, back_size,
        List.append_assoc]
      simp only [← List.cons_append, List.dropLast_concat, List.sum_cons, List.sum_reverse]
      omega

end RotationBST.BSTDeque.Deque
