module

public import RotationBST.Structures.PopTart.Chocolate.Programs
public import RotationBST.Structures.PopTart.Chocolate.Icing
public import RotationBST.Structures.PopTart.Chocolate.Mixed

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

/-- A complete Chocolate push preserves the structural and mass invariants,
retains the exact fringe order, and is realized by a constant-amortized pointer
trace in any enclosing context. -/
theorem push {stack : Layer} {level : Nat} (valid : stack.Valid level)
    {new : WeightedTree} (perfect : Perfect level new) (nonnegative : new.Nonnegative)
    (cs : List Pointer.Frame) :
    (stack.push new).Valid level ∧
      (stack.push new).decode.fringe = new.fringe ++ stack.decode.fringe ∧
      (stack.push new).decode.mass = new.mass + stack.decode.mass ∧
      Pointer.Trace ⟨.node new.tree stack.decode.tree, cs⟩
        ⟨(stack.push new).decode.tree, cs⟩ stack.pushCost ∧
      stack.pushCost + (stack.push new).potential ≤ 20 + stack.potential :=
  ⟨push_valid valid perfect nonnegative, push_fringe stack new, push_mass stack new,
    (push_trace stack new).under cs, push_amortized stack new⟩

/-- A complete pop exposes the top perfect crumb and preserves every
remaining occurrence, with exact pointer execution and amortized cost. -/
theorem pop {stack : Layer} {level : Nat} (valid : stack.Valid level) (top : stack.HasTop)
    (cs : List Pointer.Frame) :
    ∃ crumb rest, stack.pop = some (crumb, rest) ∧ Perfect level crumb ∧ crumb.Nonnegative ∧ rest.Valid level ∧
      stack.decode.fringe = crumb.fringe ++ rest.decode.fringe ∧
      stack.decode.mass = crumb.mass + rest.decode.mass ∧
      Pointer.Trace ⟨stack.decode.tree, cs⟩ ⟨.node crumb.tree rest.decode.tree, cs⟩ stack.popCost ∧
      stack.popCost + rest.potential ≤ 20 + stack.potential := by
  obtain ⟨crumb, rest, popped, perfect, nonnegative, restored⟩ := pop_valid valid top
  exact ⟨crumb, rest, popped, perfect, nonnegative, restored, pop_fringe popped, pop_mass popped,
    (pop_trace popped).under cs, pop_amortized popped⟩

end RotationBST.PopTart.Chocolate
