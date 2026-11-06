module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Preferences.Initialization.AbstractBridge

@[expose] public section
namespace RotationBST.Tango.Initialization.Results
open Wilber MarkedTree Context

theorem allowance_eq_sum (t : Tree) (lo : Nat) (w : Nat → ℝ) :
    allowance t lo w = ((List.range' lo t.size).map w).sum :=
  RotationBST.Tango.Initialization.allowance_eq_sum t lo w

theorem observed_step (t : Tree) (lo : Nat) (past : List Nat) (x : Nat) (w : Nat → ℝ)
    (valid : x < t.size) :
    observedCharge t lo (past ++ [x]) w = observedCharge t lo past w +
      firstCharge (preferenceUpdates t lo past x) w :=
  RotationBST.Tango.Initialization.observed_step t lo past x w valid

theorem observed_log (t : Tree) (past xs : List Nat) (w : Nat → ℝ)
    (valid : ∀ x ∈ xs, x < t.size) :
    observedCharge t 0 (past ++ xs) w = observedCharge t 0 past w +
      firstCharge (preferenceLog t past xs) w :=
  RotationBST.Tango.Initialization.observed_log t past xs w valid

theorem remaining_budget (t : Tree) (past xs : List Nat) (w : Nat → ℝ)
    (valid : ∀ x ∈ xs, x < t.size) (nonneg : ∀ key < t.size, 0 ≤ w key) :
    firstCharge (preferenceLog t past xs) w ≤ allowance t 0 w - observedCharge t 0 past w :=
  RotationBST.Tango.Initialization.remaining_budget t past xs w valid nonneg

theorem first_budget (t : Tree) (xs : List Nat) (w : Nat → ℝ)
    (valid : ∀ x ∈ xs, x < t.size) (nonneg : ∀ key < t.size, 0 ≤ w key) :
    firstCharge (preferenceLog t [] xs) w ≤ allowance t 0 w :=
  RotationBST.Tango.Initialization.first_budget t xs w valid nonneg

theorem first_count (t : Tree) (past xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    (preferenceLog t past xs |>.filter fun e => e.previous.isNone).length + initializations t past =
      initializations t (past ++ xs) :=
  RotationBST.Tango.Initialization.first_count t past xs valid

theorem switch_count (t : Tree) (past xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    (preferenceLog t past xs |>.filter fun e => e.previous.isSome).length + interleave t past =
      interleave t (past ++ xs) :=
  RotationBST.Tango.Initialization.switch_count t past xs valid

theorem initial_component (s : MarkedTree) (fs : List Frame)
    (unmarked : ∀ f ∈ fs, f.marked = false) (l r : MarkedTree) (next : Bool)
    (same : s.nesting = (plug fs (.node l r true true)).nesting) :
    (s.setMarksInPath fs l r true true next).1.nesting = (plug fs (.node l r (!next) next)).nesting ∧
      Rotations s.tree (s.setMarksInPath fs l r true true next).1.tree
        (s.setMarksInPath fs l r true true next).2 ∧
      ((s.setMarksInPath fs l r true true next).2 : ℝ) +
        (s.setMarksInPath fs l r true true next).1.potential - s.potential ≤
          8 * Real.logb 2 (plug fs (.node l r (!next) next)).region.size + 2 :=
  RotationBST.Tango.MarkedTree.setMarksInPath_initial_spec s fs unmarked l r next same

theorem initial_update (s reference : MarkedTree) (key : Nat) (next : Bool)
    (same : s.nesting = reference.nesting) (paths : reference.PathMarked) (valid : key < reference.tree.size)
    (first : ∃ l r fs, reference.locateKey key = some (.node l r true true, fs)) :
    ∃ size : Nat,
      size ≤ height reference.tree ∧
      (s.updatePreference reference key next).1.nesting = (reference.setPreference key next).nesting ∧
      Rotations s.tree (s.updatePreference reference key next).1.tree
        (s.updatePreference reference key next).2 ∧
      ((s.updatePreference reference key next).2 : ℝ) +
        (s.updatePreference reference key next).1.potential - s.potential ≤ 8 * Real.logb 2 size + 2 :=
  RotationBST.Tango.MarkedTree.updatePreference_initial_spec s reference key next same paths valid first

theorem empty_component (s : MarkedTree) (fs : List Frame)
    (l r : MarkedTree) (next : Bool) (empty : (if next then l else r) = .nil) :
    s.setMarksInPath fs l r true true next = (s, 0) :=
  RotationBST.Tango.MarkedTree.setMarksInPath_initial_empty s fs l r next empty

theorem component_charge (s : MarkedTree) (fs : List Frame)
    (unmarked : ∀ f ∈ fs, f.marked = false) (l r : MarkedTree) (next : Bool)
    (same : s.nesting = (plug fs (.node l r true true)).nesting) :
    (s.setMarksInPath fs l r true true next).1.nesting = (plug fs (.node l r (!next) next)).nesting ∧
      Rotations s.tree (s.setMarksInPath fs l r true true next).1.tree
        (s.setMarksInPath fs l r true true next).2 ∧
      ((s.setMarksInPath fs l r true true next).2 : ℝ) +
        (s.setMarksInPath fs l r true true next).1.potential - s.potential ≤
          if (if next then l else r) = .nil then 0
          else 8 * Real.logb 2 (plug fs (.node l r (!next) next)).region.size + 2 :=
  RotationBST.Tango.MarkedTree.setMarksInPath_initial_charge s fs unmarked l r next same

theorem empty_update_cost (s reference : MarkedTree) (key : Nat) (next : Bool)
    (l r : MarkedTree) (fs : List Frame)
    (located : reference.locateKey key = some (.node l r true true, fs))
    (empty : (if next then l else r) = .nil) :
    (s.updatePreference reference key next).2 = 0 :=
  RotationBST.Tango.MarkedTree.updatePreference_initial_empty_cost s reference key next l r fs located empty

end RotationBST.Tango.Initialization.Results

/-- info: abstract audit passed for `RotationBST.Tango.Initialization.Results`: 12 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.Initialization.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Algorithms.Tango.Algorithm.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Algorithm.Request.Abstract,
  RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Defs,
  RotationBST.Algorithms.Tango.State.Abstract,
  RotationBST.Algorithms.Tango.Preferences.Updates.Abstract,
  RotationBST.Bounds.Interleave.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Paths.Abstract,
  RotationBST.Bounds.Interleave.Wilber.Abstract,
  RotationBST.Bounds.Interleave.Transition.Defs,
  RotationBST.Algorithms.Tango.State.Preferences.Defs,
  RotationBST.Algorithms.Tango.State.Preferences.Lookup.Defs,
  RotationBST.Algorithms.Tango.State.Preferences.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.ComponentPath.Defs,
  RotationBST.Algorithms.Tango.State.ComponentPath.Address.Defs,
  RotationBST.Algorithms.Tango.State.Context.Defs,
  RotationBST.Algorithms.Tango.State.Context.Lookup.Defs,
  RotationBST.Algorithms.Tango.State.Context.Fringe.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Edits.Path.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Edits.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.Rebuild.Defs,
  RotationBST.Algorithms.Tango.State.Splay.Defs,
  RotationBST.Algorithms.Tango.State.Cut.Defs,
  RotationBST.Algorithms.Tango.State.Join.Defs,
  RotationBST.Models.Region.Abstract,
  RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract,
  RotationBST.Algorithms.Tango.Preferences.Abstract,
  RotationBST.Algorithms.Tango.Preferences.Initialization.Definitions.Abstract]
