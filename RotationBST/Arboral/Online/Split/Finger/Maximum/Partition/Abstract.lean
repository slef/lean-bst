module

public import RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Split.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Context.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Repair the smaller remaining interval after a maximum-finger local split. -/
def maximumRepairLocated (t : Multiway) (distance : Nat) : Multiway.Join.Result :=
  let location := locateMaximum t distance
  let cut := Multiway.Partition.run location.height location.focus (location.focus.size - 1 - distance)
  maximumRepairContext location.height cut.left.height cut.left.tree location.outer

/-- Split by distance from the maximum, restoring both balanced finger views. -/
def splitFromMaximum (t : Multiway) (distance : Nat) : Multiway.Partition.Cut :=
  let location := locateMaximum t distance
  let cut := Multiway.Partition.run location.height location.focus (location.focus.size - 1 - distance)
  let repaired := maximumRepairLocated t distance
  ⟨⟨repaired.tree, repaired.height⟩, cut.right, (splitLocatedMaximum t distance).2 + repaired.cost⟩

end RotationBST.Arboral.Split.Multiway.Finger
