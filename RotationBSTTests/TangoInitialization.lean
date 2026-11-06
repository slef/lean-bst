module

public import RotationBST.Algorithms.Tango.Preferences.Initialization.Abstract
public import RotationBST.Algorithms.Tango.Algorithm.Initialization.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.TangoInitialization
open Tango Initialization

private def leaf : Tree := .node .nil .nil
private def tree : Tree := .node leaf leaf

-- The first request initializes the root and its left child. Later requests
-- initialize the right child once, but switch the root's preference twice.
example : ((preferenceLog tree [0] [0, 2, 2, 0]).filter fun e => e.previous.isNone).map PreferenceUpdate.key = [2] ∧
    ((preferenceLog tree [0] [0, 2, 2, 0]).filter fun e => e.previous.isSome).map PreferenceUpdate.key = [1, 1] := by
  decide +kernel

private def weights (key : Nat) : ℝ := if key = 0 then 3 else if key = 1 then 5 else 11

-- Unequal weights detect mistakes that an aggregate event count could hide.
example : firstCharge (preferenceLog tree [] [0, 2, 2, 0]) weights = 19 ∧
    firstCharge (preferenceLog tree [0] [0, 2, 2, 0]) weights = 11 := by
  norm_num [firstCharge, preferenceLog, preferenceUpdates, tree, leaf, Tree.size,
    Wilber.regions, Wilber.leftRequests, Wilber.rightRequests, weights]

-- After the initial left request, every future valid suffix has only the
-- right leaf's credit available, irrespective of repeated requests/switches.
example (xs : List Nat) (valid : ∀ x ∈ xs, x < tree.size)
    (w : Nat → ℝ) (nonneg : ∀ key < tree.size, 0 ≤ w key) :
    firstCharge (preferenceLog tree [0] xs) w ≤ w 2 := by
  have bound := Results.remaining_budget tree [0] xs w valid nonneg
  norm_num [allowance, observedCharge, tree, leaf, Tree.size,
    Wilber.regions, Wilber.leftRequests, Wilber.rightRequests] at bound
  exact bound

-- Once all reference nodes have been observed, first-setting events cease
-- for every future valid sequence, although preference switches continue.
example (xs : List Nat) (valid : ∀ x ∈ xs, x < tree.size) :
    (preferenceLog tree [0, 2] xs |>.filter fun e => e.previous.isNone) = [] := by
  apply List.eq_nil_of_length_eq_zero
  have count := Results.first_count tree [0, 2] xs valid
  have bound := initializations_le_size tree ([0, 2] ++ xs)
  have seen : initializations tree [0, 2] = 3 := by decide +kernel
  rw [seen] at count
  change initializations tree ([0, 2] ++ xs) ≤ 3 at bound
  omega

-- The compiled first preference joins the root and left singleton without
-- rotating the physical tree; future bounds must not charge an entire cut.
example : ((MarkedTree.initial tree).updatePreference (MarkedTree.initial tree) 1 true).2 = 0 := by
  decide +kernel

example : ∃ size : Nat, size ≤ 2 ∧
    ((MarkedTree.initial tree).updatePreference (MarkedTree.initial tree) 1 true).1.nesting =
      ((MarkedTree.initial tree).setPreference 1 true).nesting ∧
    Rotations (MarkedTree.initial tree).tree
      ((MarkedTree.initial tree).updatePreference (MarkedTree.initial tree) 1 true).1.tree
      ((MarkedTree.initial tree).updatePreference (MarkedTree.initial tree) 1 true).2 ∧
    (((MarkedTree.initial tree).updatePreference (MarkedTree.initial tree) 1 true).2 : ℝ) +
      ((MarkedTree.initial tree).updatePreference (MarkedTree.initial tree) 1 true).1.potential -
      (MarkedTree.initial tree).potential ≤ 8 * Real.logb 2 size + 2 := by
  exact Results.initial_update (MarkedTree.initial tree) (MarkedTree.initial tree) 1 true rfl
    (by simp [MarkedTree.PathMarked, MarkedTree.initial, tree, leaf]) (by decide +kernel)
    ⟨MarkedTree.initial leaf, MarkedTree.initial leaf, [], rfl⟩

private def markedLeaf : MarkedTree := .node .nil .nil true true
private def chain (bottom : MarkedTree) : MarkedTree :=
  .node (.node bottom .nil false true) .nil false true
private def path : List Context.Frame := [.left .nil false true, .left .nil false true]

-- The previous generic join splays the minimum of a three-node component
-- even though the selected child is empty. The specialized first setting
-- performs no rotations and preserves the entire marked state instead.
example : ((chain markedLeaf).unmarkInPath path (.left .nil true true)).2 = 2 ∧
    (chain markedLeaf).setMarksInPath path .nil .nil true true true = (chain markedLeaf, 0) ∧
    (chain markedLeaf).updatePreference (chain markedLeaf) 0 true = (chain markedLeaf, 0) := by
  decide +kernel

-- The zero-cost result survives compilation through a nested component.
private def nested : MarkedTree := .node (chain markedLeaf) .nil true true

example : nested.updatePreference nested 0 true = (nested, 0) := by decide +kernel

-- A nonempty first join still executes its boundary splay. This guards
-- against accidentally skipping all first preferences or losing a child.
private def nonemptyChild : MarkedTree := .node markedLeaf .nil true true

example : ((chain nonemptyChild).updatePreference (chain nonemptyChild) 1 true).2 = 2 := by
  decide +kernel

-- Charge the actual evolving reference: the first root join costs 10,
-- the later root switch costs 18, and both leaf initializations cost zero.
private theorem mixed_charge : logCharge (MarkedTree.initial tree) (preferenceLog tree [] [0, 2]) = 28 := by
  change (8 * Real.logb 2 (2 : ℝ) + 2) + (0 + ((14 * Real.logb 2 (2 : ℝ) + 4) + (0 + 0))) = 28
  norm_num

example : logCharge (MarkedTree.initial tree) (preferenceLog tree [] [0, 0]) = 10 := by
  change (8 * Real.logb 2 (2 : ℝ) + 2) + (0 + 0) = 10
  norm_num

-- A singleton universe has no nonempty initialization join.
example : logCharge (MarkedTree.initial leaf) (preferenceLog leaf [] [0, 0, 0]) = 0 := by
  change (0 : ℝ) + 0 = 0
  ring

-- Charge classification follows reference marks, not supplied log metadata.
example : logCharge (MarkedTree.initial tree) [⟨1, none, true⟩] =
    logCharge (MarkedTree.initial tree) [⟨1, some false, true⟩] := rfl

-- The complete executable policy inherits the refined charge. Both requests
-- are physically served; no separate initialization allowance is appended.
example : Execution tree [0, 2] ((policy tree).run [0, 2]).1.tree ((policy tree).run [0, 2]).2 ∧
    (((policy tree).run [0, 2]).2 : ℝ) ≤ 36 := by
  have valid : ∀ x ∈ [0, 2], x < tree.size := by
    intro x member
    change x < 3
    simp at member
    omega
  have bound := Tango.Algorithm.Initialization.Results.run_bound (policy tree) (fun _ _ _ => rfl) [0, 2] valid
  rw [mixed_charge] at bound
  norm_num [tree, leaf, height] at bound
  exact ⟨((policy tree).run_spec [0, 2] valid).1, by exact_mod_cast bound⟩

-- Classification uses the actual reference marks even when two supplied log
-- entries both falsely claim to be first settings of the same node.
private def inconsistentLog : List PreferenceUpdate := [⟨1, none, true⟩, ⟨1, none, false⟩]

example : firstCount (MarkedTree.initial tree) inconsistentLog = 1 ∧
    laterCount (MarkedTree.initial tree) inconsistentLog = 1 := by decide +kernel

example : firstLogCharge (MarkedTree.initial tree) inconsistentLog = 10 := by
  change (8 * Real.logb 2 (2 : ℝ) + 2) + (0 + 0) = 10
  norm_num

-- Generated logs agree with the semantic split: three initialized nodes,
-- one interleave switch, and only the nonempty first join has a charge.
example : firstCount (MarkedTree.initial tree) (preferenceLog tree [] [0, 2]) = 3 ∧
    laterCount (MarkedTree.initial tree) (preferenceLog tree [] [0, 2]) = 1 := by decide +kernel

example : firstLogCharge (MarkedTree.initial tree) (preferenceLog tree [] [0, 2]) = 10 := by
  change (8 * Real.logb 2 (2 : ℝ) + 2) + (0 + (0 + (0 + 0))) = 10
  norm_num

-- An arbitrary valid suffix cannot initialize any node a second time after
-- the prefix has already observed all three reference nodes.
example (xs : List Nat) (valid : ∀ x ∈ xs, x < tree.size) :
    firstCount (MarkedTree.canonical tree 0 [0, 2]) (preferenceLog tree [0, 2] xs) = 0 := by
  have history : ∀ x ∈ [0, 2], x < tree.size := by
    intro x member; change x < 3; simp at member; omega
  have count := Tango.Algorithm.Initialization.Results.firstCount_generated tree [0, 2] xs history valid
  have seen : initializations tree [0, 2] = 3 := by decide +kernel
  have bound := initializations_le_size tree ([0, 2] ++ xs)
  rw [seen] at count
  change initializations tree ([0, 2] ++ xs) ≤ 3 at bound
  omega

-- Incomplete balanced levels and inorder indexing determine each node's
-- local credit; it is not the common height of the whole reference tree.
example : heightSum (balanced 0) = 0 ∧ heightSum (balanced 10) = 20 ∧
    ((List.range 10).map (heightAt (balanced 10))) = [1, 2, 3, 1, 2, 4, 1, 2, 3, 1] ∧
    heightAt (balanced 10) 10 = 0 := by
  decide +kernel

-- The three-node tree has credits 2,10,2. Repeated accesses and switches
-- never spend any node's credit twice; a nonempty history consumes it.
example : firstCharge (preferenceLog tree [] [0, 0, 2, 2, 0]) (localCredit tree) = 14 ∧
    firstCharge (preferenceLog tree [0] [0, 2, 2, 0]) (localCredit tree) = 2 := by
  norm_num [firstCharge, preferenceLog, preferenceUpdates, tree, leaf, Tree.size,
    Wilber.regions, Wilber.leftRequests, Wilber.rightRequests, localCredit, heightAt, height]

-- The structural allowance is independent of the absolute address offset.
example : allowance tree 17 (fun key => localCredit tree (key - 17)) = 14 := by
  rw [Local.Results.allowance_localCredit]
  norm_num [localAllowance, height, tree, leaf]

example (n : Nat) (past xs : List Nat) (valid : ∀ key ∈ xs, key < n) :
    firstCharge (preferenceLog (balanced n) past xs) (localCredit (balanced n)) +
      observedCharge (balanced n) 0 past (localCredit (balanced n)) ≤ 42 * n := by
  have bound := Local.Results.balanced_remainingCharge n past xs valid
  linarith

-- A top-down first setting may already belong to an ancestor component.
-- Its target component is larger than its own reference subtree height;
-- applying the component-root theorem here would silently lose a hypothesis.
private def ancestorJoined : MarkedTree :=
  (MarkedTree.initial (balanced 7)).setPreference 3 true

example : firstAt ancestorJoined 1 = true ∧
    (ancestorJoined.setPreference 1 true).region.size = 3 ∧
    heightAt ancestorJoined.tree 1 = 2 := by
  decide +kernel

end RotationBST.Tests.TangoInitialization
