module

public import RotationBST.Arboral.Online.Split.Finger.Locate.Split.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Repair.Context.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Repair the larger remaining interval after splitting the located subtree. -/
def repairLocated (t : Multiway) (rank : Nat) : Multiway.Join.Result :=
  let location := locate t rank
  let cut := Multiway.Partition.run location.height location.focus rank
  repairContext location.height cut.right.height cut.right.tree location.outer

/-- Split from the minimum finger, then restore balance throughout the enclosing
context. Both outputs are reusable balanced minimum-finger trees. -/
def splitFromMinimum (t : Multiway) (rank : Nat) : Multiway.Partition.Cut :=
  let location := locate t rank
  let cut := Multiway.Partition.run location.height location.focus rank
  let repaired := repairLocated t rank
  ⟨cut.left, ⟨repaired.tree, repaired.height⟩, (splitLocated t rank).2 + repaired.cost⟩

end RotationBST.Arboral.Split.Multiway.Finger
