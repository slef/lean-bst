module

public import RotationBST.Structures.HeavyPath.Finger.Definitions.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Top.Definitions.Abstract

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Pair
open PopTart

def potential (p : Pair) : Nat := p.lower.potential + p.upper.potential

/-- The left source child is already exposed as the root of the innermost
payload. Its left child stays below; its right child enters the other stack. -/
noncomputable def downLeft (p : Pair) (a b : Tree) (lowerCharge upperCharge : ℝ) : Pair :=
  ⟨p.lower.replaceTop (.leaf a.mirror lowerCharge), p.upper.push (.leaf b upperCharge)⟩

def leftExposeCost (p : Pair) : Nat := match p.lower.topTail with | none => 2 | some _ => 4
noncomputable def downLeftCost (p : Pair) : Nat := p.leftExposeCost + p.upper.pushCost + 2

def flip (p : Pair) : Pair := ⟨p.upper, p.lower⟩

/-- The reflected transfer uses the same physical operation in the opposite
orientation. The old finger node supplies the pushed separator. -/
noncomputable def downRight (p : Pair) (a b : Tree) (lowerCharge upperCharge : ℝ) : Pair :=
  (p.flip.downLeft b.mirror a.mirror upperCharge lowerCharge).flip

noncomputable def downRightCost (p : Pair) : Nat := p.flip.downLeftCost

end RotationBST.HeavyPath.Finger.Pair
