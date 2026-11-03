module

public import RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger

/-- Conversion with an enclosing separator, carrying its larger-key remainder
through the recursion instead of repeatedly rotating completed prefixes. -/
def openConversionCost : Multiway → Nat
  | .nil => 0
  | .two a _ => openConversionCost a + 1
  | .three a _ _ => openConversionCost a + 2
  | .four a _ _ _ => openConversionCost a + 3

/-- Conversion at the root needs no enclosing-separator rotation. -/
def conversionCost : Multiway → Nat
  | .nil => 0
  | .two a _ | .three a _ _ => openConversionCost a
  | .four a _ _ _ => openConversionCost a + 1

end RotationBST.Geometric.Split.Multiway.Finger
