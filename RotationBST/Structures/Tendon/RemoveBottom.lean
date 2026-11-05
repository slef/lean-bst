module

public import RotationBST.Structures.Tendon.Bottom

@[expose] public section
namespace RotationBST.Tendon.State

theorem removeBottom_lower {d : State} {cs : List Pointer.Frame} {g : Tree}
    (h : d.Represents (.right g :: cs)) (bottom : Tree) :
    ∃ (e : State) (k : Nat), e.Represents cs ∧ k + e.potential ≤ 180 + d.potential ∧
      Pointer.Trace ⟨d.tree bottom, []⟩ ⟨e.tree (.node g bottom), []⟩ k := by
  have hl : d.lower.fringe.dropLast = lowerFringe cs ++ [g] := h.1
  have hu : d.upper.fringe.tail = upperFringe cs := h.2
  let u := Pointer.plug d.upper.minContext bottom
  let q := d.lower.withMax u
  have positive : 0 < q.size := by
    have len := congrArg List.length hl
    simp only [List.length_dropLast, BSTDeque.Deque.fringe_length, List.length_append,
      List.length_singleton] at len
    simpa only [q, BSTDeque.Deque.withMax_size] using (show 0 < d.lower.size by omega)
  obtain ⟨a, r, pop⟩ := q.popBack_exists positive
  have fringe := BSTDeque.Deque.popBack_fringe pop
  simp only [q, BSTDeque.Deque.withMax_fringe, hl] at fringe
  have aeq : a = u := by
    have eq := congrArg List.getLast? fringe
    simpa only [List.getLast?_concat, Option.some.injEq] using eq.symm
  subst a
  have hr : r.fringe = lowerFringe cs ++ [g] := (List.append_cancel_right fringe).symm
  let e : State := ⟨r.withMax .nil, d.upper⟩
  have rep : e.Represents cs := by
    constructor
    · simp [e, BSTDeque.Deque.withMax_fringe, hr]
    · exact hu
  have treeR : r.tree = Pointer.plug e.lower.maxContext g := by
    simpa only [e, BSTDeque.Deque.withMax_context] using BSTDeque.Deque.tree_of_fringe_max hr
  obtain ⟨i, hi, first⟩ := BSTDeque.Deque.popBack_trace pop
  obtain ⟨j, hj, second⟩ := (lower_exchange e.lower g u).1
  obtain ⟨k, hk, third⟩ := (upper_exchange d.upper g bottom).1
  have third' := third.inContext (by simp) (Pointer.plug_ne_nil _ (by simp)) e.lower.maxContext
  rw [treeR] at first
  have all := (first.append second).append third'
  refine ⟨e, i + j + (e.lower.maxContext.length + k + e.lower.maxContext.length), rep, ?_, ?_⟩
  · have len := (r.withMax .nil).maxContext_length
    simp only [q, BSTDeque.Deque.withMax_potential] at hi
    simp only [e, potential, BSTDeque.Deque.withMax_potential]
    omega
  · simpa only [q, BSTDeque.Deque.withMax_tree, u, tree, context, Pointer.plug_append, e] using all

theorem removeBottom_upper {d : State} {cs : List Pointer.Frame} {g : Tree}
    (h : d.Represents (.left g :: cs)) (bottom : Tree) :
    ∃ (e : State) (k : Nat), e.Represents cs ∧ k + e.potential ≤ 132 + d.potential ∧
      Pointer.Trace ⟨d.tree bottom, []⟩ ⟨e.tree (.node bottom g), []⟩ k := by
  have hl : d.lower.fringe.dropLast = lowerFringe cs := h.1
  have hu : d.upper.fringe.tail = g :: upperFringe cs := h.2
  let q := d.upper.withMin bottom
  have positive : 0 < q.size := by
    have len := congrArg List.length hu
    simp only [List.length_tail, BSTDeque.Deque.fringe_length, List.length_cons] at len
    simpa only [q, BSTDeque.Deque.withMin_size] using (show 0 < d.upper.size by omega)
  obtain ⟨a, r, pop⟩ := q.popFront_exists positive
  have fringe := BSTDeque.Deque.popFront_fringe pop
  simp only [q, BSTDeque.Deque.withMin_fringe, hu, List.cons.injEq] at fringe
  obtain ⟨rfl, hr⟩ := fringe
  let e : State := ⟨d.lower, r.withMin .nil⟩
  have rep : e.Represents cs := by
    constructor
    · exact hl
    · simp [e, BSTDeque.Deque.withMin_fringe, ← hr]
  have treeR : r.tree = Pointer.plug e.upper.minContext g := by
    simpa only [e, BSTDeque.Deque.withMin_context] using BSTDeque.Deque.tree_of_fringe_min hr.symm
  obtain ⟨i, hi, first⟩ := BSTDeque.Deque.popFront_trace pop
  obtain ⟨j, hj, second⟩ := (upper_exchange e.upper bottom g).1
  have qne : q.tree ≠ .nil := by
    cases qh : q with
    | empty => simp [qh, BSTDeque.Deque.size] at positive
    | node => simp [BSTDeque.Deque.tree, BSTDeque.Deque.skeleton, Pointer.Lazy.Skeleton.tree]
  rw [treeR] at first
  have all := (first.append second).inContext qne (Pointer.plug_ne_nil _ (by simp)) d.lower.maxContext
  refine ⟨e, d.lower.maxContext.length + (i + j) + d.lower.maxContext.length, rep, ?_, ?_⟩
  · have len := d.lower.maxContext_length
    simp only [q, BSTDeque.Deque.withMin_potential] at hi
    simp only [e, potential, BSTDeque.Deque.withMin_potential]
    omega
  · simpa only [q, BSTDeque.Deque.withMin_tree, tree, context, Pointer.plug_append, e] using all

/-- Expose the actual reference path's innermost node as the new bottom
endpoint. Rebuilding, reassociation, and pointer navigation are all charged. -/
theorem removeBottom {d : State} {cs : List Pointer.Frame} (f : Pointer.Frame)
    (h : d.Represents (f :: cs)) (bottom : Tree) :
    ∃ (e : State) (k : Nat), e.Represents cs ∧ k + e.potential ≤ 180 + d.potential ∧
      Pointer.Trace ⟨d.tree bottom, []⟩ ⟨e.tree (Pointer.plug [f] bottom), []⟩ k := by
  cases f with
  | right g => exact removeBottom_lower h bottom
  | left g =>
    obtain ⟨e, k, rep, bound, trace⟩ := removeBottom_upper h bottom
    exact ⟨e, k, rep, by omega, trace⟩

end RotationBST.Tendon.State
