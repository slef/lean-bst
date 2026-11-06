module

public import RotationBST.Structures.PopTart.Cherry.Programs
public import RotationBST.Structures.PopTart.Cherry.Keys
public import RotationBST.Structures.PopTart.Abstract

@[expose] public section
namespace RotationBST.PopTart.Cherry
open WeightedTree

/-- Push has the exact weighted fringe, a valid result, a concrete pointer
realization, and constant amortized rebalancing cost. -/
theorem push {level : Nat} {layers : Layers} (valid : Valid level layers)
    {crumb : WeightedTree} (perfect : Perfect level crumb) (bottom : WeightedTree) :
    Valid level (layers.push crumb) ∧
      ((layers.push crumb).decode bottom).fringe = crumb.fringe ++ (layers.decode bottom).fringe ∧
      Pointer.Trace ⟨.node crumb.tree (layers.decode bottom).tree, []⟩
        ⟨((layers.push crumb).decode bottom).tree, []⟩ layers.pushCost ∧
      layers.pushCost + (layers.push crumb).potential ≤ 10 + layers.potential :=
  ⟨push_valid valid perfect, push_fringe layers crumb bottom, push_trace layers crumb bottom,
    push_amortized layers crumb⟩

/-- A nonempty valid stack pops successfully, retaining the weighted fringe
order and the exact exposed separator, with a constant amortized cost. -/
theorem pop {level : Nat} {layers : Layers} (valid : Valid level layers) (nonempty : layers ≠ .nil)
    (bottom : WeightedTree) :
    ∃ crumb rest, layers.pop = some (crumb, rest) ∧ Perfect level crumb ∧ Valid level rest ∧
      (layers.decode bottom).fringe = crumb.fringe ++ (rest.decode bottom).fringe ∧
      Pointer.Trace ⟨(layers.decode bottom).tree, []⟩
        ⟨.node crumb.tree (rest.decode bottom).tree, []⟩ layers.popCost ∧
      layers.popCost + rest.potential ≤ 10 + layers.potential := by
  obtain ⟨crumb, rest, popped, perfect, validRest⟩ := pop_valid valid nonempty
  exact ⟨crumb, rest, popped, perfect, validRest, pop_fringe popped bottom, pop_trace popped bottom,
    pop_amortized popped⟩

end RotationBST.PopTart.Cherry
