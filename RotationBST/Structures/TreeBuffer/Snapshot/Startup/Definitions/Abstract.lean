module

public import RotationBST.Structures.TreeBuffer.Nodes.Initialization.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Startup

/-- Initialization followed by a shared-node snapshot operation. Both fingers
start at the original root. The initializer returns there before the second
phase, which uses exactly its output tree. `n` is the supplied universe size. -/
def Execution (tree : Tree) (n : Nat) (fields : Nat → IntervalMetadata.Bounds) (data : Nat → Nat)
    (final : Shared.State Nat 2) (events : List (Cells.Event Nat)) (total : Nat) : Prop :=
  ∃ ready setupCost work,
    Nodes.Initialization.runFuel (8 * n)
      (Nodes.Initialization.initial (Nodes.Initialization.raw fields data tree 0) n) = some (setupCost, ready) ∧
    Nodes.Initialization.Run
      (Nodes.Initialization.initial (Nodes.Initialization.raw fields data tree 0) n) ready setupCost ∧
    Nodes.Initialization.tick ready = none ∧ ready.cursor.context = [] ∧
    Shared.Trace ⟨ready.cursor.tree, fun _ => Streaming.rootPosition tree⟩ final events work ∧
    total = setupCost + work

end RotationBST.TreeBuffer.Snapshot.Startup
