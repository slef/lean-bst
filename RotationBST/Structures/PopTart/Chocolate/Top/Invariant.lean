module

public import RotationBST.Structures.PopTart.Chocolate.Top.Proofs
public import RotationBST.Bounds.StaticTree.Trace.Invariant
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate

/-- Replacing the front payload preserves a supplied structural prefix bound
through its optional enclosing separator, with the same navigation overhead. -/
theorem replaceTop_within (stack : Layer) (new : WeightedTree) {cost factor constant : Nat}
    (factorPositive : 1 ≤ factor)
    (oldNonempty : stack.top.tree ≠ .nil) (newNonempty : new.tree ≠ .nil)
    (trace : Pointer.TraceWithin (fun t => t.size = stack.top.tree.size ∧
      ∀ x, Tree.depth t x ≤ factor * Tree.depth stack.top.tree x + constant)
      ⟨stack.top.tree, []⟩ ⟨new.tree, []⟩ cost) :
    ∃ total, total ≤ cost + 2 ∧
      Pointer.TraceWithin (fun t => t.size = stack.decode.tree.size ∧
        ∀ x, Tree.depth t x ≤ factor * Tree.depth stack.decode.tree x + constant)
        ⟨stack.decode.tree, []⟩ ⟨(stack.replaceTop new).decode.tree, []⟩ total := by
  rw [decode_top stack, replaceTop_decode]
  cases tail : stack.topTail with
  | none => exact ⟨cost, by omega, trace⟩
  | some suffix =>
    have lifted := StaticTree.Trace.within_embed [.left suffix.tree]
      factorPositive trace oldNonempty newNonempty
    refine ⟨cost + 2, le_rfl, ?_⟩
    simpa [Pointer.plug, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lifted

end RotationBST.PopTart.Chocolate
