module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.Algorithm.Definitions.Abstract
public import RotationBST.Tango.Algorithm.Request

@[expose] public section
namespace RotationBST.Tango
open MarkedTree

/-- The executable causal policy: compile preference edits and splay the key. -/
def policy (reference : Tree) : Policy reference where
  step past s x := s.serve reference past x
  correct past s x maintained history valid := serve_spec s reference past x maintained history valid

end RotationBST.Tango

namespace RotationBST.Tango.Algorithm.Executable.Results
open MarkedTree

/-- The computed request visits its key and preserves the next-history invariant,
with one logarithmic charge per preference edit and one final splay charge. -/
theorem request (s : MarkedTree) (reference : Tree) (past : List Nat) (x : Nat)
    (maintained : Maintains s reference past) (history : ∀ y ∈ past, y < reference.size)
    (valid : x < reference.size) :
    Access s.tree (s.serve reference past x).1.tree x (s.serve reference past x).2 ∧
      Maintains (s.serve reference past x).1 reference (past ++ [x]) ∧
      ((s.serve reference past x).2 : ℝ) + (s.serve reference past x).1.potential - s.potential ≤
        (preferenceUpdates reference 0 past x).length * (14 * Real.logb 2 (height reference) + 4) +
          (3 * Real.logb 2 (height reference) + 1) :=
  serve_spec s reference past x maintained history valid

end RotationBST.Tango.Algorithm.Executable.Results

#check_bst_abstract RotationBST.Tango.Algorithm.Executable.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.Algorithm.Definitions.Abstract,
  RotationBST.Tango.Algorithm.Request.Abstract,
  RotationBST.Tango.State.Definitions.Abstract, RotationBST.Tango.State.Nesting.Abstract,
  RotationBST.Tango.State.Canonical.Abstract, RotationBST.Tango.Preferences.Updates.Abstract,
  RotationBST.Tango.Definitions.Abstract, RotationBST.Tango.Paths.Abstract,
  RotationBST.Tango.Wilber.Abstract, RotationBST.Tango.Transition.Abstract,
  RotationBST.Tango.State.Preferences.Abstract, RotationBST.Tango.State.Preferences.Lookup.Abstract,
  RotationBST.Tango.State.Preferences.Algorithm.Abstract,
  RotationBST.Tango.State.ComponentPath.Abstract, RotationBST.Tango.State.ComponentPath.Address.Abstract,
  RotationBST.Tango.State.Context.Abstract, RotationBST.Tango.State.Context.Lookup.Abstract,
  RotationBST.Tango.State.Context.Fringe.Abstract,
  RotationBST.Tango.State.Nesting.Edits.Path.Algorithm.Abstract,
  RotationBST.Tango.State.Nesting.Edits.Algorithm.Abstract,
  RotationBST.Tango.State.Rebuild.Abstract, RotationBST.Tango.State.Splay.Abstract,
  RotationBST.Tango.State.Cut.Abstract, RotationBST.Tango.State.Join.Abstract,
  RotationBST.Arboral.Treap.Regions.Abstract, RotationBST.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract, RotationBST.Pointer.Traces,
  RotationBST.Pointer.Machine.Abstract, RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Potential.Abstract]
