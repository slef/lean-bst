module

public import RotationBST.Structures.PopTart.Vanilla.Depth

@[expose] public section
namespace RotationBST.PopTart.Vanilla

/-- Push prepends exactly one weighted fringe slot, preserving all old ones. -/
theorem push_fringe (t : Tree) (w : ℝ) (stack : WeightedTree) :
    (push t w stack).skeleton.fringe = t :: stack.skeleton.fringe := rfl

/-- A successful pop exposes the first slot and retains the entire suffix. -/
theorem pop_fringe {stack tail : WeightedTree} {t : Tree} {w : ℝ}
    (exposed : pop stack = some ((t, w), tail)) :
    stack.skeleton.fringe = t :: tail.skeleton.fringe := by
  cases stack with
  | leaf => simp [pop] at exposed
  | node l r =>
    cases l with
    | node => simp [pop] at exposed
    | leaf t' w' =>
      simp only [pop, Option.some.injEq, Prod.mk.injEq] at exposed
      rcases exposed with ⟨⟨rfl, rfl⟩, rfl⟩
      rfl

/-- Vanilla needs no rebalancing instructions: the supplied/exposed separator
is already at the root. This also holds in any enclosing pointer context. -/
theorem operation {stack tail : WeightedTree} (op : Operation stack tail) (cs : List Pointer.Frame) :
    Pointer.Trace ⟨op.input, cs⟩ ⟨op.output, cs⟩ 0 := by
  cases op with
  | push => exact .refl
  | pop stack tail t w exposed =>
    cases stack with
    | leaf => simp [pop] at exposed
    | node l r =>
      cases l with
      | node => simp [pop] at exposed
      | leaf t' w' =>
        simp only [pop, Option.some.injEq, Prod.mk.injEq] at exposed
        rcases exposed with ⟨⟨rfl, rfl⟩, rfl⟩
        exact .refl

end RotationBST.PopTart.Vanilla
