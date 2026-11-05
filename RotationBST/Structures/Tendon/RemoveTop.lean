module

public import RotationBST.Structures.Tendon.Top

@[expose] public section
namespace RotationBST.Tendon.State

theorem removeTop_lower {d : State} {cs : List Pointer.Frame} {g : Tree}
    (h : d.Represents (cs ++ [.right g])) (bottom : Tree) :
    ∃ (e : State) (k : Nat), e.Represents cs ∧ k + e.potential ≤ 80 + d.potential ∧
      Pointer.Trace ⟨d.tree bottom, []⟩ ⟨.node g (e.tree bottom), []⟩ k := by
  have hl : d.lower.fringe.dropLast = g :: lowerFringe cs := by
    simpa [lowerFringe_append, lowerFringe] using h.1
  have hu : d.upper.fringe.tail = upperFringe cs := by
    simpa [upperFringe_append, upperFringe] using h.2
  let u := Pointer.plug d.upper.minContext bottom
  let q := d.lower.withMax u
  have positive : 0 < q.size := by
    have len := congrArg List.length hl
    simp only [List.length_dropLast, BSTDeque.Deque.fringe_length, List.length_cons] at len
    simpa only [q, BSTDeque.Deque.withMax_size] using (show 0 < d.lower.size by omega)
  obtain ⟨a, r, pop⟩ := q.popFront_exists positive
  have fringe := BSTDeque.Deque.popFront_fringe pop
  simp only [q, BSTDeque.Deque.withMax_fringe, hl, List.cons_append, List.cons.injEq] at fringe
  obtain ⟨rfl, hr⟩ := fringe
  let e : State := ⟨r.withMax .nil, d.upper⟩
  have rep : e.Represents cs := by
    constructor
    · simp [e, BSTDeque.Deque.withMax_fringe, ← hr]
    · exact hu
  have treeR : r.tree = e.tree bottom := by
    rw [BSTDeque.Deque.tree_of_fringe_max hr.symm]
    simp only [e, tree, context, BSTDeque.Deque.withMax_context, Pointer.plug_append, u]
  obtain ⟨k, bound, trace⟩ := BSTDeque.Deque.popFront_trace pop
  refine ⟨e, k, rep, ?_, ?_⟩
  · simp only [q, BSTDeque.Deque.withMax_potential] at bound
    simp only [e, potential, BSTDeque.Deque.withMax_potential]
    omega
  · simpa only [q, BSTDeque.Deque.withMax_tree, treeR, tree, context,
      Pointer.plug_append, u] using trace

theorem removeTop_upper {d : State} {cs : List Pointer.Frame} {g : Tree}
    (h : d.Represents (cs ++ [.left g])) (bottom : Tree) :
    ∃ (e : State) (k : Nat), e.Represents cs ∧ k + e.potential ≤ 132 + d.potential ∧
      Pointer.Trace ⟨d.tree bottom, []⟩ ⟨.node (e.tree bottom) g, []⟩ k := by
  have hl : d.lower.fringe.dropLast = lowerFringe cs := by
    simpa [lowerFringe_append, lowerFringe] using h.1
  have hu : d.upper.fringe.tail = upperFringe cs ++ [g] := by
    simpa [upperFringe_append, upperFringe] using h.2
  let q := d.upper.withMin bottom
  have positive : 0 < q.size := by
    have len := congrArg List.length hu
    simp only [List.length_tail, BSTDeque.Deque.fringe_length, List.length_append,
      List.length_singleton] at len
    simpa only [q, BSTDeque.Deque.withMin_size] using (show 0 < d.upper.size by omega)
  obtain ⟨a, r, pop⟩ := q.popBack_exists positive
  have fringe := BSTDeque.Deque.popBack_fringe pop
  simp only [q, BSTDeque.Deque.withMin_fringe, hu, ← List.cons_append] at fringe
  have aeq : a = g := by
    have eq := congrArg List.getLast? fringe
    simpa only [List.getLast?_concat, Option.some.injEq] using eq.symm
  subst a
  have hr : r.fringe = bottom :: upperFringe cs := (List.append_cancel_right fringe).symm
  let e : State := ⟨d.lower, r.withMin .nil⟩
  have rep : e.Represents cs := by
    constructor
    · exact hl
    · simp [e, BSTDeque.Deque.withMin_fringe, hr]
  have treeR : r.tree = Pointer.plug (r.withMin .nil).minContext bottom := by
    simpa only [BSTDeque.Deque.withMin_context] using BSTDeque.Deque.tree_of_fringe_min hr
  obtain ⟨k, bound, trace⟩ := BSTDeque.Deque.popBack_trace pop
  obtain ⟨a, b, eq⟩ : ∃ a b, q.tree = .node a b := by
    cases qh : q with
    | empty => simp [qh, BSTDeque.Deque.size] at positive
    | node => exact ⟨_, _, rfl⟩
  have down := Pointer.descend d.lower.maxContext a b
  rw [← eq] at down
  have mid := trace.under d.lower.maxContext
  have up := Pointer.ascend d.lower.maxContext r.tree g
  obtain ⟨j, hj, last⟩ := (lower_exchange d.lower r.tree g).2
  have all := ((down.append mid).append up).append last
  refine ⟨e, d.lower.maxContext.length + k + d.lower.maxContext.length + j, rep, ?_, ?_⟩
  · have len := d.lower.maxContext_length
    simp only [q, BSTDeque.Deque.withMin_potential] at bound
    simp only [e, potential, BSTDeque.Deque.withMin_potential]
    omega
  · simpa only [q, BSTDeque.Deque.withMin_tree, treeR, e, tree, context, Pointer.plug_append,
      Pointer.Config.under, List.nil_append] using all

/-- Expose the reference path's outermost node in constant amortized pointer
cost. Both orientations preserve all side subtrees and the remaining path. -/
theorem removeTop {d : State} {cs : List Pointer.Frame} (f : Pointer.Frame)
    (h : d.Represents (cs ++ [f])) (bottom : Tree) :
    ∃ (e : State) (k : Nat), e.Represents cs ∧ k + e.potential ≤ 132 + d.potential ∧
      Pointer.Trace ⟨d.tree bottom, []⟩ ⟨Pointer.plug [f] (e.tree bottom), []⟩ k := by
  cases f with
  | left g => exact removeTop_upper h bottom
  | right g =>
    obtain ⟨e, k, rep, bound, trace⟩ := removeTop_lower h bottom
    exact ⟨e, k, rep, by omega, trace⟩

end RotationBST.Tendon.State
