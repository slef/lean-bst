module

public import RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Shared.CellRefinement

def Represents {α : Type} {fingers : Nat} (actual : Shared.State α fingers) (model : Cells.State α)
    (i : Fin fingers) : Prop :=
  actual.Valid model.data ∧ actual.tree.erase = model.scan.tree ∧ actual.position i = model.scan.position

end RotationBST.TreeBuffer.Shared.CellRefinement
