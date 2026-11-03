module

public import RotationBST.Algorithms.Simulation.Supernode.Extraction.Defs
public import RotationBST.Algorithms.Simulation.Supernode.Accounting.Defs

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode

/-- The causal stored-state update: extract this row, then rebuild its exposed
keys as one fresh supernode. No future requests or priorities are inspected. -/
def nextState (state : Nested) (keys : Finset Nat) : Nested :=
  (extractRow keys 0 state).1.rebuild

end RotationBST.Geometric.Online.Supernode
