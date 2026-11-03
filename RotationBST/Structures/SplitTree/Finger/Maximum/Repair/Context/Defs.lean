module

public import RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Frame.Defs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger
open Context

/-- Repair ancestors until the focused interval regains its expected height.
The untouched suffix is then reattached without rotations. -/
def maximumRepairContext : Nat → Nat → Multiway → List Frame → Multiway.Join.Result
  | _, actual, focus, [] => ⟨focus, actual, 0⟩
  | expected, actual, focus, f :: fs =>
      if actual = expected then
        ⟨plug (f :: fs) focus, expected + (f :: fs).length, 0⟩
      else
        let step := maximumRepairFrame expected actual focus f
        let result := maximumRepairContext (expected + 1) step.height step.tree fs
        let cost := match fs with
          | [] => step.cost
          | _ :: _ => maximumRepairFrameOpenCost expected actual focus f
        ⟨result.tree, result.height, cost + result.cost⟩

end RotationBST.Geometric.Split.Multiway.Finger
