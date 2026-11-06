module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Preferences.Initialization.Local.AbstractBridge

@[expose] public section
namespace RotationBST.Tango.Initialization.Local.Results
open MarkedTree Context

theorem heightSum_cap (t : Tree) (h : Nat) (cap : height t ≤ h) :
    heightSum t + h + 2 ≤ 2 ^ (h + 1) :=
  RotationBST.Tango.Initialization.heightSum_cap t h cap

theorem balanced_heightSum (n : Nat) : heightSum (balanced n) ≤ 4 * n :=
  RotationBST.Tango.Initialization.balanced_heightSum n

theorem allowance_localCredit (t : Tree) (lo : Nat) :
    allowance t lo (fun key => localCredit t (key - lo)) = localAllowance t :=
  RotationBST.Tango.Initialization.allowance_localCredit t lo

theorem balanced_localAllowance (n : Nat) : localAllowance (balanced n) ≤ 42 * n :=
  RotationBST.Tango.Initialization.balanced_localAllowance n

theorem balanced_firstCharge (n : Nat) (xs : List Nat) (valid : ∀ key ∈ xs, key < n) :
    firstCharge (preferenceLog (balanced n) [] xs) (localCredit (balanced n)) ≤ 42 * n :=
  RotationBST.Tango.Initialization.balanced_firstCharge n xs valid

theorem balanced_remainingCharge (n : Nat) (past xs : List Nat)
    (valid : ∀ key ∈ xs, key < n) :
    firstCharge (preferenceLog (balanced n) past xs) (localCredit (balanced n)) ≤
      42 * n - observedCharge (balanced n) 0 past (localCredit (balanced n)) :=
  RotationBST.Tango.Initialization.balanced_remainingCharge n past xs valid

theorem root_component_charge (s l r : MarkedTree) (next : Bool)
    (paths : (MarkedTree.node l r true true).PathMarked)
    (same : s.nesting = (MarkedTree.node l r true true).nesting) :
    (s.setMarksInPath [] l r true true next).1.nesting =
      (MarkedTree.node l r (!next) next).nesting ∧
      Rotations s.tree (s.setMarksInPath [] l r true true next).1.tree
        (s.setMarksInPath [] l r true true next).2 ∧
      ((s.setMarksInPath [] l r true true next).2 : ℝ) +
        (s.setMarksInPath [] l r true true next).1.potential - s.potential ≤
          localCredit (.node l.tree r.tree) l.tree.size :=
  RotationBST.Tango.Initialization.root_component_charge s l r next paths same

end RotationBST.Tango.Initialization.Local.Results

/-- info: abstract audit passed for `RotationBST.Tango.Initialization.Local.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.Initialization.Local.Results allowing [RotationBST.Models.Rotation.Abstract,
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
  RotationBST.Algorithms.Tango.Preferences.Initialization.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Reference.Abstract,
  RotationBST.Algorithms.Tango.Preferences.Initialization.Local.Definitions.Abstract]
