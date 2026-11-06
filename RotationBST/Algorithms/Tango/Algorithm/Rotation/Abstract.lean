module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Algorithm.Rotation.AbstractBridge

@[expose] public section
namespace RotationBST.Tango.Algorithm.Rotation.Results

/-- A causal rotation algorithm follows the marked policy exactly from its
reference tree. Any other same-size initial tree pays at most one 2n reset.
Reconstructing private marks from history has uncharged abstract planning cost. -/
theorem rotation_algorithm {reference : Tree} (p : Policy reference) :
    ∃ a : RotationBST.Algorithm,
      (∀ xs, (∀ x ∈ xs, x < reference.size) →
        a.runFrom [] reference xs = ((p.run xs).1.tree, (p.run xs).2)) ∧
      ∀ saved : Tree, saved.size = reference.size → ∀ xs, (∀ x ∈ xs, x < reference.size) →
        a.totalCost saved xs ≤ xs.length + (p.run xs).2 + 2 * saved.size :=
  p.rotation_algorithm

end RotationBST.Tango.Algorithm.Rotation.Results

/-- info: abstract audit passed for `RotationBST.Tango.Algorithm.Rotation.Results`: 1 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.Algorithm.Rotation.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Algorithms.Tango.Algorithm.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Reference.Abstract,
  RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Defs,
  RotationBST.Algorithms.Tango.State.Abstract,
  RotationBST.Algorithms.Tango.Preferences.Updates.Abstract,
  RotationBST.Bounds.Interleave.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Paths.Abstract,
  RotationBST.Bounds.Interleave.Wilber.Abstract,
  RotationBST.Bounds.Interleave.Transition.Defs,
  RotationBST.Models.Region.Abstract,
  RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract,
  RotationBST.Models.Online.Abstract]
