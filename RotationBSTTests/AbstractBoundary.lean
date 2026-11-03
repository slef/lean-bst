module

import RotationBST.Audit.Check
import RotationBST.Algorithms.Splay.Algorithm.Abstract

/-! Regression tests for the local abstract dependency audit. -/

namespace RotationBSTTests.AbstractBoundary.Good

def size (t : RotationBST.Tree) : Nat := t.size

/-- info: abstract audit passed for `RotationBSTTests.AbstractBoundary.Good`: 1 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBSTTests.AbstractBoundary.Good allowing [RotationBST.Models.Rotation.Abstract]

end RotationBSTTests.AbstractBoundary.Good

namespace RotationBSTTests.AbstractBoundary.Bad

def hidden (t : RotationBST.Tree) := RotationBST.Splay.run t 0

/-- error: abstract audit: `RotationBSTTests.AbstractBoundary.Bad.hidden` depends on implementation declaration `RotationBST.Splay.run` from `RotationBST.Algorithms.Splay.Algorithm.Abstract` -/
#guard_msgs in
#check_bst_abstract RotationBSTTests.AbstractBoundary.Bad allowing [RotationBST.Models.Rotation.Abstract]

end RotationBSTTests.AbstractBoundary.Bad

namespace RotationBSTTests.AbstractBoundary.Transitive

/-- This wrapper's type is elementary, but its body reaches the splay implementation. -/
def wrapper (t : RotationBST.Tree) := RotationBST.Splay.run t 0

namespace Claim

def cost (t : RotationBST.Tree) := (wrapper t).2

/-- error: abstract audit: `RotationBSTTests.AbstractBoundary.Transitive.Claim.cost` depends on declaration `RotationBSTTests.AbstractBoundary.Transitive.wrapper` outside `RotationBSTTests.AbstractBoundary.Transitive.Claim` -/
#guard_msgs in
#check_bst_abstract RotationBSTTests.AbstractBoundary.Transitive.Claim allowing [RotationBST.Models.Rotation.Abstract]

end Claim
end RotationBSTTests.AbstractBoundary.Transitive
