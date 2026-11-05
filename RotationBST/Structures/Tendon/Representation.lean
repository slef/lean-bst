module

public import RotationBST.Structures.Tendon.Definitions.Abstract
public import RotationBST.Structures.BSTDeque.Boundary

@[expose] public section
namespace RotationBST.Tendon

open Pointer.Lazy

theorem lowerFringe_append (cs ds : List Pointer.Frame) :
    lowerFringe (cs ++ ds) = lowerFringe ds ++ lowerFringe cs := by
  induction cs with
  | nil => simp [lowerFringe]
  | cons c cs ih => cases c <;> simp [lowerFringe, ih, List.append_assoc]

theorem upperFringe_append (cs ds : List Pointer.Frame) :
    upperFringe (cs ++ ds) = upperFringe cs ++ upperFringe ds := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [upperFringe, ih]

theorem maxContext_upper (q : BSTDeque.Deque) : upperFringe q.maxContext = [] := by
  cases q with
  | empty => rfl
  | node front a b back => cases back <;> rfl

theorem minContext_lower (q : BSTDeque.Deque) : lowerFringe q.minContext = [] := by
  cases q with
  | empty => rfl
  | node front a b back => cases front <;> rfl

theorem path_fringe (cs : List Pointer.Frame) (s : Skeleton) :
    (s.under cs).fringe = lowerFringe cs ++ s.fringe ++ upperFringe cs := by
  induction cs generalizing s with
  | nil => simp [Skeleton.under, lowerFringe, upperFringe]
  | cons c cs ih =>
    cases c <;> simp [Skeleton.under, lowerFringe, upperFringe, ih, Skeleton.fringe,
      List.append_assoc]

theorem path_length (cs : List Pointer.Frame) :
    (lowerFringe cs).length + (upperFringe cs).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [lowerFringe, upperFringe] <;> omega

theorem path_offset (cs : List Pointer.Frame) :
    Pointer.offset cs = (lowerFringe cs).length + ((lowerFringe cs).map Tree.size).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp [lowerFringe, Pointer.offset, ih]
    omega

namespace State

theorem context_length (d : State) : d.context.length ≤ 4 := by
  have h := d.lower.maxContext_length
  have g := d.upper.minContext_length
  simp only [context, List.length_append]
  omega

theorem skeleton_tree (d : State) (bottom : Tree) : (d.skeleton bottom).tree = d.tree bottom := by
  simp only [skeleton, tree, context, Pointer.plug_append]
  rw [← BSTDeque.Deque.maxContext_fill, ← BSTDeque.Deque.minContext_fill]
  rfl

theorem skeleton_fringe (d : State) (bottom : Tree) :
    (d.skeleton bottom).fringe = d.lower.fringe.dropLast ++ [bottom] ++ d.upper.fringe.tail := by
  simp [skeleton, Skeleton.fillMax_fringe, Skeleton.fillMin_fringe, Skeleton.fringe,
    List.append_assoc]

theorem represents_size {d : State} {cs : List Pointer.Frame} (h : d.Represents cs) :
    d.lower.size = (lowerFringe cs).length ∧ d.upper.size = (upperFringe cs).length := by
  have l := congrArg List.length h.1
  have r := congrArg List.length h.2
  simp only [List.length_dropLast, BSTDeque.Deque.fringe_length] at l
  simp only [List.length_tail, BSTDeque.Deque.fringe_length] at r
  omega

theorem represents_empty {d : State} (h : d.Represents []) :
    d.context = [] ∧ d.potential = 0 := by
  have sizes := represents_size h
  rcases d with ⟨lower, upper⟩
  cases lower <;> cases upper <;>
    simp_all [lowerFringe, upperFringe, BSTDeque.Deque.size, context, potential,
      BSTDeque.Deque.minContext, BSTDeque.Deque.maxContext, BSTDeque.Deque.potential]

/-- Compression preserves the global rank of the entire bottom subtree. -/
theorem represents_offset {d : State} {cs : List Pointer.Frame} (h : d.Represents cs) :
    Pointer.offset d.context = Pointer.offset cs := by
  rw [context, Pointer.offset_append, BSTDeque.Deque.minContext_offset,
    Nat.zero_add, BSTDeque.Deque.maxContext_offset, h.1, (represents_size h).1, path_offset]

theorem represents_fringe {d : State} {cs : List Pointer.Frame} (h : d.Represents cs)
    (bottom : Tree) :
    ((Skeleton.hole bottom).under cs).fringe = (d.skeleton bottom).fringe := by
  rw [path_fringe, skeleton_fringe, h.1, h.2]
  rfl

theorem ofPath_represents (cs : List Pointer.Frame) : (ofPath cs).Represents cs := by
  unfold Represents ofPath
  simp [BSTDeque.Deque.balance_fringe]

theorem ofPath_potential (cs : List Pointer.Frame) : (ofPath cs).potential ≤ 64 := by
  have l := BSTDeque.Deque.balance_potential (lowerFringe cs ++ [.nil])
  have r := BSTDeque.Deque.balance_potential (.nil :: upperFringe cs)
  exact Nat.add_le_add l r

/-- Any matching representation is reachable by a legal pointer execution whose
cost depends on the path length, not the sizes of its side subtrees. -/
theorem compress_trace {d : State} {cs : List Pointer.Frame} (h : d.Represents cs)
    (bottom : Tree) : ∃ k, k ≤ 16 * cs.length ∧
      Pointer.Trace ⟨Pointer.plug cs bottom, []⟩ ⟨d.tree bottom, []⟩ k := by
  obtain ⟨k, bound, trace⟩ := Skeleton.reshape _ _ (represents_fringe h bottom)
  refine ⟨k, ?_, ?_⟩
  · simpa [Skeleton.under_size, Skeleton.size] using bound
  · simpa only [Skeleton.under_tree, Skeleton.tree, skeleton_tree] using trace

/-- The endpoint is reached in at most four moves, with its original inorder key. -/
theorem visit_bottom {d : State} {cs : List Pointer.Frame} (h : d.Represents cs)
    (l r : Tree) :
    Pointer.Trace ⟨d.tree (.node l r), []⟩ ⟨.node l r, d.context⟩ d.context.length ∧
      (Pointer.Config.mk (.node l r) d.context).key? = some (Pointer.offset cs + l.size) ∧
      d.context.length ≤ 4 := by
  refine ⟨Pointer.descend d.context l r, ?_, context_length d⟩
  simp only [Pointer.Config.key?, represents_offset h]

end State
end RotationBST.Tendon
