module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Algorithm.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Algorithm.Request

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
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.Tango.Algorithm.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Algorithm.Request.Abstract,
  RotationBST.Algorithms.Tango.State.Defs, RotationBST.Algorithms.Tango.State.Nesting.Defs,
  RotationBST.Algorithms.Tango.State.Canonical.Defs, RotationBST.Algorithms.Tango.Preferences.Updates.Abstract,
  RotationBST.Bounds.Interleave.Definitions.Abstract, RotationBST.Algorithms.Tango.Definitions.Abstract, RotationBST.Algorithms.Tango.Paths.Abstract,
  RotationBST.Bounds.Interleave.Wilber.Abstract, RotationBST.Bounds.Interleave.Transition.Abstract,
  RotationBST.Algorithms.Tango.State.Preferences.Defs, RotationBST.Algorithms.Tango.State.Preferences.Lookup.Defs,
  RotationBST.Algorithms.Tango.State.Preferences.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.ComponentPath.Defs, RotationBST.Algorithms.Tango.State.ComponentPath.Address.Defs,
  RotationBST.Algorithms.Tango.State.Context.Defs, RotationBST.Algorithms.Tango.State.Context.Lookup.Defs,
  RotationBST.Algorithms.Tango.State.Context.Fringe.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Edits.Path.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Edits.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.Rebuild.Defs, RotationBST.Algorithms.Tango.State.Splay.Defs,
  RotationBST.Algorithms.Tango.State.Cut.Defs, RotationBST.Algorithms.Tango.State.Join.Defs,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract, RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract]
