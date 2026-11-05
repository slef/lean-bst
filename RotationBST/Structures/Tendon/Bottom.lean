module

public import RotationBST.Structures.Tendon.Exchange
public import RotationBST.Structures.BSTDeque.Operations

@[expose] public section
namespace RotationBST.Tendon

/-- Push a maximum while retaining a separate open right boundary. -/
theorem pushBack_at_max (q : BSTDeque.Deque) (g bottom : Tree) :
    ∃ k, k ≤ 2 ∧ Pointer.Trace ⟨.node (Pointer.plug q.maxContext g) bottom, []⟩
      ⟨Pointer.plug ((q.withMax g).pushBack .nil).maxContext bottom, []⟩ k := by
  cases q with
  | empty => exact ⟨0, by omega, .refl⟩
  | node front a b back =>
    cases back <;> exact ⟨2, by omega, .step .downLeft (.step .rotateLeftChild .refl)⟩

/-- Push a minimum while retaining a separate open left boundary. -/
theorem pushFront_at_min (q : BSTDeque.Deque) (g bottom : Tree) :
    ∃ k, k ≤ 2 ∧ Pointer.Trace ⟨.node bottom (Pointer.plug q.minContext g), []⟩
      ⟨Pointer.plug ((q.withMin g).pushFront .nil).minContext bottom, []⟩ k := by
  cases q with
  | empty => exact ⟨0, by omega, .refl⟩
  | node front a b back =>
    cases front <;> exact ⟨2, by omega, .step .downRight (.step .rotateRightChild .refl)⟩

namespace State

theorem addBottom_represents {d : State} {cs : List Pointer.Frame} (h : d.Represents cs)
    (f : Pointer.Frame) : (d.addBottom f).Represents (f :: cs) := by
  cases f with
  | right g =>
    simp only [addBottom, Represents, BSTDeque.Deque.pushBack_fringe,
      BSTDeque.Deque.withMax_fringe, List.dropLast_concat, lowerFringe, upperFringe, h.1, h.2]
    trivial
  | left g =>
    simp only [addBottom, Represents, BSTDeque.Deque.pushFront_fringe,
      BSTDeque.Deque.withMin_fringe, List.tail_cons, lowerFringe, upperFringe, h.1, h.2]
    trivial

theorem addBottom_potential (d : State) (f : Pointer.Frame) :
    (d.addBottom f).potential ≤ d.potential + 32 := by
  cases f with
  | right g =>
    have bound := (d.lower.withMax g).pushBack_potential .nil
    simp only [BSTDeque.Deque.withMax_potential] at bound
    simp only [addBottom, potential]
    omega
  | left g =>
    have bound := (d.upper.withMin g).pushFront_potential .nil
    simp only [BSTDeque.Deque.withMin_potential] at bound
    simp only [addBottom, potential]
    omega

/-- Move the old bottom's parent into the compressed tendon. Only the two short
boundary paths and the selected deque operation are touched. -/
theorem addBottom_trace (d : State) (f : Pointer.Frame) (bottom : Tree) :
    ∃ k, k ≤ 102 ∧ Pointer.Trace ⟨d.tree (Pointer.plug [f] bottom), []⟩
      ⟨(d.addBottom f).tree bottom, []⟩ k := by
  cases f with
  | right g =>
    let u := Pointer.plug d.upper.minContext bottom
    obtain ⟨i, hi, first⟩ := (upper_exchange d.upper g bottom).2
    have first' := first.inContext (Pointer.plug_ne_nil _ (by simp)) (by simp) d.lower.maxContext
    obtain ⟨j, hj, second⟩ := (lower_exchange d.lower g u).2
    obtain ⟨k, hk, third⟩ := pushBack_at_max d.lower g u
    have all := (first'.append second).append third
    refine ⟨d.lower.maxContext.length + i + d.lower.maxContext.length + j + k, ?_, ?_⟩
    · have := d.lower.maxContext_length; omega
    · simpa only [u, tree, context, addBottom, Pointer.plug_append, Pointer.plug] using all
  | left g =>
    obtain ⟨i, hi, first⟩ := (upper_exchange d.upper bottom g).2
    obtain ⟨j, hj, second⟩ := pushFront_at_min d.upper g bottom
    have all := (first.append second).inContext (Pointer.plug_ne_nil _ (by simp))
      (by
        cases h : d.upper with
        | empty => simp [BSTDeque.Deque.withMin, BSTDeque.Deque.pushFront,
            BSTDeque.Deque.minContext, Pointer.plug]
        | node front a b back =>
          cases front <;> simp [BSTDeque.Deque.withMin, BSTDeque.Deque.pushFront,
            BSTDeque.Deque.minContext, Pointer.plug]) d.lower.maxContext
    refine ⟨d.lower.maxContext.length + (i + j) + d.lower.maxContext.length, ?_, ?_⟩
    · have := d.lower.maxContext_length; omega
    · simpa only [tree, context, addBottom, Pointer.plug_append, Pointer.plug] using all

theorem addBottom_amortized (d : State) (f : Pointer.Frame) (bottom : Tree) :
    ∃ k, k + (d.addBottom f).potential ≤ 134 + d.potential ∧
      Pointer.Trace ⟨d.tree (Pointer.plug [f] bottom), []⟩
        ⟨(d.addBottom f).tree bottom, []⟩ k := by
  obtain ⟨k, bound, trace⟩ := d.addBottom_trace f bottom
  have := d.addBottom_potential f
  exact ⟨k, by omega, trace⟩

end State
end RotationBST.Tendon
