module

public import RotationBST.Structures.Tendon.Exchange
public import RotationBST.Structures.BSTDeque.Operations

@[expose] public section
namespace RotationBST.Tendon

theorem pushFront_open (q : BSTDeque.Deque) (g bottom : Tree) :
    ∃ k, k ≤ 2 ∧ Pointer.Trace ⟨.node g (Pointer.plug q.maxContext bottom), []⟩
      ⟨Pointer.plug (q.pushFront g).maxContext bottom, []⟩ k := by
  cases q with
  | empty => exact ⟨0, by omega, .refl⟩
  | node front a b back =>
    cases back <;> exact ⟨2, by omega, .step .downRight (.step .rotateRightChild .refl)⟩

theorem pushBack_open (q : BSTDeque.Deque) (g bottom : Tree) :
    ∃ k, k ≤ 2 ∧ Pointer.Trace ⟨.node (Pointer.plug q.minContext bottom) g, []⟩
      ⟨Pointer.plug (q.pushBack g).minContext bottom, []⟩ k := by
  cases q with
  | empty => exact ⟨0, by omega, .refl⟩
  | node front a b back =>
    cases front <;> exact ⟨2, by omega, .step .downLeft (.step .rotateLeftChild .refl)⟩

namespace State

theorem addTop_represents {d : State} {cs : List Pointer.Frame} (h : d.Represents cs)
    (f : Pointer.Frame) : (d.addTop f).Represents (cs ++ [f]) := by
  cases f with
  | right g =>
    simp only [addTop, Represents, BSTDeque.Deque.pushFront_fringe,
      List.dropLast_cons_of_ne_nil d.lower.fringe_ne_nil,
      lowerFringe_append, upperFringe_append, lowerFringe, upperFringe,
      List.nil_append, List.singleton_append, List.append_nil, h.1, h.2]
    trivial
  | left g =>
    simp only [addTop, Represents, BSTDeque.Deque.pushBack_fringe,
      List.tail_append_of_ne_nil d.upper.fringe_ne_nil,
      lowerFringe_append, upperFringe_append, lowerFringe, upperFringe,
      List.nil_append, h.1, h.2]
    trivial

theorem addTop_potential (d : State) (f : Pointer.Frame) :
    (d.addTop f).potential ≤ d.potential + 32 := by
  cases f with
  | right g =>
    have := d.lower.pushFront_potential g
    simp only [addTop, potential]
    omega
  | left g =>
    have := d.upper.pushBack_potential g
    simp only [addTop, potential]
    omega

/-- Absorb one top node with constant worst-case pointer work. The state update
preserves the side-subtree representation and increases potential by at most 32. -/
theorem addTop_trace (d : State) (f : Pointer.Frame) (bottom : Tree) :
    ∃ k, k ≤ 54 ∧ Pointer.Trace ⟨Pointer.plug [f] (d.tree bottom), []⟩
      ⟨(d.addTop f).tree bottom, []⟩ k := by
  cases f with
  | right g =>
    obtain ⟨k, hk, trace⟩ := pushFront_open d.lower g (Pointer.plug d.upper.minContext bottom)
    refine ⟨k, by omega, ?_⟩
    simpa only [tree, context, addTop, Pointer.plug_append, Pointer.plug] using trace
  | left g =>
    let u := Pointer.plug d.upper.minContext bottom
    obtain ⟨i, hi, first⟩ := (lower_exchange d.lower u g).1
    obtain ⟨j, hj, mid⟩ := pushBack_open d.upper g bottom
    have mid' := mid.under d.lower.maxContext
    have down := Pointer.descend d.lower.maxContext u g
    have next_nonempty : ∃ a b, Pointer.plug (d.upper.pushBack g).minContext bottom = .node a b := by
      cases h : d.upper with
      | empty => exact ⟨_, _, rfl⟩
      | node front a b back => cases front <;> exact ⟨_, _, rfl⟩
    obtain ⟨a, b, eq⟩ := next_nonempty
    have up := Pointer.ascend d.lower.maxContext a b
    rw [← eq] at up
    have all := ((first.append down).append mid').append up
    refine ⟨i + d.lower.maxContext.length + j + d.lower.maxContext.length, ?_, ?_⟩
    · have := d.lower.maxContext_length; omega
    · simpa only [u, tree, context, addTop, Pointer.plug_append, Pointer.plug,
        Pointer.Config.under, List.nil_append] using all

theorem addTop_amortized (d : State) (f : Pointer.Frame) (bottom : Tree) :
    ∃ k, k + (d.addTop f).potential ≤ 86 + d.potential ∧
      Pointer.Trace ⟨Pointer.plug [f] (d.tree bottom), []⟩
        ⟨(d.addTop f).tree bottom, []⟩ k := by
  obtain ⟨k, bound, trace⟩ := d.addTop_trace f bottom
  have := d.addTop_potential f
  exact ⟨k, by omega, trace⟩

end State
end RotationBST.Tendon
