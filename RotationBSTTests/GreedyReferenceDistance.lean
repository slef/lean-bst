module

public import RotationBST.Algorithms.GreedyASS.Reference.Distance.Abstract

@[expose] public section
namespace RotationBST.Tests.GreedyReferenceDistance
open Geometric.GreedyASS.Reference
open Geometric.GreedyASS.Reference.Distance

private def pair : Tree := .node .nil .nil
private def quad : Tree := .node pair pair
private def eight : Tree := .node quad quad
private def leftComponent : Component := ⟨0, quad⟩

-- A leaf has depth zero but node-counted self-distance one. The searched
-- singleton is a real component, and its later blue value will be two.
example : depth .nil 9 9 = 0 ∧ toLCA .nil 9 9 9 9 = 1 ∧
    toRoot ⟨9, .nil⟩ 9 = 1 := by decide
example : (⟨6, .nil⟩ : Component) ∈ forest eight 0 6 ∧
    toRoot ⟨6, .nil⟩ 6 = 1 := by decide

-- Both sides of Fact 3.1 can be strict. Weakly ordered coincident leaves
-- are also covered, without manufacturing a positive edge distance.
example : toLCA eight 0 1 0 3 = 3 ∧ toLCA eight 0 1 0 7 = 4 ∧
    toLCA eight 0 5 4 7 = 3 ∧ toLCA eight 0 5 0 7 = 4 := by decide
example : toLCA eight 0 1 0 3 ≤ toLCA eight 0 1 0 7 ∧
    toLCA eight 0 3 1 7 ≤ toLCA eight 0 3 0 7 :=
  Distance.Results.ordered eight 0 0 1 3 7 (by decide) (by decide) (by decide)
example : toLCA eight 0 3 3 3 = 1 := by decide

-- Equal component shapes at different offsets retain different occurrences.
example : lca eight 10 10 13 = ⟨10, quad⟩ ∧ lca eight 10 14 17 = ⟨14, quad⟩ ∧
    lcaDepth eight 10 10 13 = 1 ∧ lcaDepth eight 10 14 17 = 1 := by decide
example : Occurs eight 10 ⟨14, quad⟩ 1 := .right (.root quad 14)

-- Being below the component root is equivalent to enclosing endpoints both
-- belonging to that component. Crossing its boundary makes the distance larger.
example : toLCA eight 0 1 0 3 ≤ toRoot leftComponent 1 ↔
    leftComponent.Contains 0 ∧ leftComponent.Contains 3 :=
  (Distance.Results.component eight 0 6 0 1 3 (c := leftComponent)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1
example : toRoot leftComponent 1 < toLCA eight 0 1 0 7 ↔
    ¬ leftComponent.Contains 0 ∨ ¬ leftComponent.Contains 7 :=
  (Distance.Results.component eight 0 6 0 1 7 (c := leftComponent)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2

-- Translated, unbalanced trees exercise offsets and unequal leaf depths.
example : depth (.node .nil pair) 10 10 = 1 ∧ depth (.node .nil pair) 10 11 = 2 ∧
    toLCA (.node .nil pair) 10 11 10 12 = 3 := by decide
example : toRoot ⟨10, .node .nil pair⟩ 12 = toRoot ⟨11, pair⟩ 12 + 1 :=
  (Distance.Results.merge .nil pair 10 12).2 (by decide)

-- The LCA computation is total, but its common-ancestor specification requires
-- valid ranks. There is no leaf 1 in the singleton rooted at offset zero.
example : ¬ (lca .nil 0 0 1).Contains 1 := by decide

end RotationBST.Tests.GreedyReferenceDistance
