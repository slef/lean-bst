module

public import RotationBST.Algorithms.OptimalLazyFinger.Abstract
public import RotationBST.Bounds.LazyFinger.Edges.Abstract
public import RotationBST.Structures.PrefixSum.Abstract

@[expose] public section
namespace RotationBST.Tests.OptimalLazyFinger
open RotationBST

private def leaf : Tree := .node .nil .nil
private def balanced : Tree := .node leaf leaf

-- Outside-to-outside transitions do not enter the subtree, even if their
-- numerical rank interval surrounds it.
example : LazyFinger.edgeMovement balanced 2 0 6 = 0 := by decide
example : LazyFinger.edgeMovement balanced 2 2 6 = 2 := by decide
example : LazyFinger.crossings 2 4 2 [0, 3, 4, 2] = 4 := by decide

-- The virtual initial key pays precisely the otherwise absent incoming edge.
example : LazyFinger.intervalCost (fun a b => LazyFinger.crossings a b 3 [1]) balanced 0 = 1 := by
  decide
example : LazyFinger.cost balanced [1] = 1 := by decide

-- Empty instances and repeated keys exercise the distinct startup conventions.
example : OptimalLazyFinger.tree 0 [] = .nil := by decide
example : LazyFinger.cost (OptimalLazyFinger.tree 3 [2, 2, 2]) [2, 2, 2] = 3 := by decide
example : LazyFinger.costFrom (OptimalLazyFinger.treeFrom 3 0 [0, 0]) 0 [0, 0] = 2 := by decide

-- Equal single-key frequencies do not determine an optimal lazy-finger tree:
-- the optimizer responds to transition order.
example : OptimalLazyFinger.tree 3 [0, 1, 2] = .node .nil (.node .nil leaf) := by decide
example : OptimalLazyFinger.tree 3 [0, 2, 1] = .node .nil (.node leaf .nil) := by decide

-- This numerical optimum follows from the verified constructor, not a supplied
-- optimality certificate or an enumeration assumption.
example : LazyFinger.optimalCost 3 [0, 2, 1] = 5 := by
  have h := (OptimalLazyFinger.Results.root_start 3 [0, 2, 1] (by decide)).2
  have hc : LazyFinger.cost (OptimalLazyFinger.tree 3 [0, 2, 1]) [0, 2, 1] = 5 := by decide
  exact h.symm.trans hc

-- Prefix queries retain both directed orientations and handle empty rectangles.
example : PrefixSum.rectangle (PrefixSum.build (fun i j => 10 * i + j) 4 3) 1 3 1 4 = 102 := by
  decide
example : PrefixSum.rectangle (PrefixSum.build (fun _ _ => 1) 5 5) 4 5 4 5 = 1 := by decide
example : PrefixSum.rectangle (PrefixSum.build (fun i j => i + j) 3 2) 1 1 0 3 = 0 := by decide

example : PrefixSum.get (OptimalLazyFinger.Preprocessing.frequencies 4 3 [0, 1, 0, 0]) 3 0 = 1 := by
  decide
example : PrefixSum.get (OptimalLazyFinger.Preprocessing.frequencies 4 3 [0, 1, 0, 0]) 0 3 = 0 := by
  decide
example : OptimalLazyFinger.Preprocessing.toll
    (OptimalLazyFinger.Preprocessing.prepare 4 3 [0, 1, 0, 0]) 4 0 1 = 3 := by decide
example : OptimalLazyFinger.Preprocessing.toll
    (OptimalLazyFinger.Preprocessing.prepare 4 3 [0, 1, 0, 0]) 4 0 3 = 1 := by decide
example : OptimalLazyFinger.Preprocessing.toll
    (OptimalLazyFinger.Preprocessing.prepare 4 3 [0, 1, 0, 0]) 4 0 0 = 0 := by decide

end RotationBST.Tests.OptimalLazyFinger
