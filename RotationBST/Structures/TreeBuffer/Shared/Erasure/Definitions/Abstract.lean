module

public import RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract
public import RotationBST.Models.Multifinger.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Shared

/-- Forget cell and routing fields while retaining the one tree and every
persistent finger. Erasure is a specification, not a runtime traversal. -/
def State.erase {α : Type} {fingers : Nat} (s : State α fingers) : Multifinger.State fingers :=
  ⟨s.tree.erase, s.position⟩

end RotationBST.TreeBuffer.Shared
