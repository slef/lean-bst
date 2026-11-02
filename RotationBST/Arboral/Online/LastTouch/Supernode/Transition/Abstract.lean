module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Extraction.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Accounting.Abstract

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- The causal stored-state update: extract this row, then rebuild its exposed
keys as one fresh supernode. No future requests or priorities are inspected. -/
def nextState (state : Nested) (keys : Finset Nat) : Nested :=
  (extractRow keys 0 state).1.rebuild

end RotationBST.Arboral.Online.Supernode
