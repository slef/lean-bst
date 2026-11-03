module

public import RotationBST.Algorithms.Tango.Algorithm.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Algorithm.Executable.AbstractBridge

@[expose] public section
namespace RotationBST.Tango
open MarkedTree

/-- The executable causal policy: compile preference edits and splay the key. -/
def policy (reference : Tree) : Policy reference where
  step past s x := s.serve reference past x
  correct past s x maintained history valid := serve_spec s reference past x maintained history valid

end RotationBST.Tango
