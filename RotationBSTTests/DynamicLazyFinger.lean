module

public import RotationBST.Bounds.LazyFinger.Dynamic.Abstract
public import RotationBST.Models.Pointer.Abstract

@[expose] public section
namespace RotationBST.Tests.DynamicLazyFinger

private def leaf : Tree := .node .nil .nil
private def balanced : Tree := .node (.node leaf leaf) (.node leaf leaf)
private def chain : Tree := .node (.node (.node leaf .nil) .nil) .nil

-- A common ancestor strictly below the root: a root-return walk would overcount.
example : LazyFinger.distance balanced 0 2 = 2 := by decide
example : ∃ a b : Pointer.Config, a.tree = balanced ∧ b.tree = balanced ∧
    a.key? = some 0 ∧ b.key? = some 2 ∧ Pointer.Trace a b 2 :=
  LazyFinger.Dynamic.Results.walk balanced 0 2 (by decide) (by decide)

-- Both recursive branches and a walk crossing the root are exercised.
example : ∃ a b : Pointer.Config, a.tree = balanced ∧ b.tree = balanced ∧
    a.key? = some 4 ∧ b.key? = some 6 ∧ Pointer.Trace a b 2 :=
  LazyFinger.Dynamic.Results.walk balanced 4 6 (by decide) (by decide)
example : ∃ a b : Pointer.Config, a.tree = balanced ∧ b.tree = balanced ∧
    a.key? = some 0 ∧ b.key? = some 6 ∧ Pointer.Trace a b 4 :=
  LazyFinger.Dynamic.Results.walk balanced 0 6 (by decide) (by decide)
example : ∃ a b : Pointer.Config, a.tree = balanced ∧ b.tree = balanced ∧
    a.key? = some 3 ∧ b.key? = some 0 ∧ Pointer.Trace a b 2 :=
  LazyFinger.Dynamic.Results.walk balanced 3 0 (by decide) (by decide)

-- Repeated accesses require no movement but still incur their request units.
example : ∃ q : Nat, Multifinger.Execution
    (⟨balanced, fun _ : Fin 1 => 0⟩ : Multifinger.State 1) [0, 0, 2, 2]
    ⟨balanced, fun _ => q⟩ 6 :=
  LazyFinger.Dynamic.Results.persistent balanced 0 [0, 0, 2, 2] (by decide)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide)

example : ∃ u k, Pointer.Execution balanced [0, 2, 6, 6] u k ∧ k ≤ 464 * 12 :=
  LazyFinger.Dynamic.Results.same_tree balanced [0, 2, 6, 6]
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide)

-- Startup works between different shapes and is charged as actual instructions.
example : ∃ k, k ≤ 64 ∧ Pointer.Trace ⟨chain, []⟩ ⟨.node leaf (.node .nil leaf), []⟩ k :=
  Pointer.Results.reshape chain (.node leaf (.node .nil leaf)) (by decide)
example : ∃ u k, Pointer.Execution chain [0] u k ∧
    k ≤ 64 + 464 * LazyFinger.optimalCost 4 [0] :=
  LazyFinger.Dynamic.Results.optimal chain [0]
    (by intro x hx; simp at hx; subst x; decide)

example : ∃ u k, Pointer.Execution leaf [0, 0] u k ∧
    k ≤ 480 * LazyFinger.optimalCost 1 [0, 0] :=
  LazyFinger.Dynamic.Results.long_sequence leaf [0, 0]
    (by intro x hx; simp at hx; subst x; decide) (by decide)

-- An empty request list does not create a fictitious startup request.
example : ∃ u k, Pointer.Execution chain [] u k ∧
    k ≤ 64 + 464 * LazyFinger.cost (.node leaf (.node .nil leaf)) [] :=
  LazyFinger.Dynamic.Results.reference chain (.node leaf (.node .nil leaf)) []
    (by decide) (by simp)
example : ∃ u k, Pointer.Execution .nil [] u k ∧
    k ≤ 16 * Tree.nil.size + 464 * LazyFinger.optimalCost Tree.nil.size [] :=
  LazyFinger.Dynamic.Results.optimal .nil [] (by simp)

end RotationBST.Tests.DynamicLazyFinger
