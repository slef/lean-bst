module

public import RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs
public import RotationBST.Structures.SplitTree.Multiway.Extract.Defs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Finger rotations for extracting inside a larger enclosing interval.
Descending through the comparison spine itself adds no rotations. -/
def extractOpenCost : Nat → Multiway → Nat
  | 0, _ => 0
  | fuel + 1, t =>
      match t.rootMerge with
      | some contracted => 1 + extractOpenCost fuel contracted
      | none =>
          let prepared := (t.repairFirst).1
          repairOpenCost t + if firstChild prepared = .nil then 0 else extractOpenCost fuel (firstChild prepared)

/-- Finger rotations for extraction at the root, without an enclosing separator. -/
def extractViewCost : Nat → Multiway → Nat
  | 0, _ => 0
  | fuel + 1, t =>
      match t.rootMerge with
      | some contracted => extractViewCost fuel contracted
      | none =>
          let prepared := (t.repairFirst).1
          repairViewCost t + if firstChild prepared = .nil then 0 else extractOpenCost fuel (firstChild prepared)

/-- Remove the minimum while maintaining the concrete finger representation.
The marked multiway endpoint is the same as in ordinary minimum extraction;
this count charges the rotations in the finger BST. -/
def extractView (t : Multiway) : Multiway × Nat :=
  ((t.extractMin).1, extractViewCost (t.nodes + 1) t)

end RotationBST.Arboral.Split.Multiway.Finger
