module

public import RotationBST.Arboral.Online.Split.Finger.Repair.Frame.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

/-- Repair ancestors until the focused interval regains its expected height.
The untouched suffix is then reattached without rotations. -/
def repairContext : Nat → Nat → Multiway → List Frame → Multiway.Join.Result
  | _, actual, focus, [] => ⟨focus, actual, 0⟩
  | expected, actual, focus, f :: fs =>
      if actual = expected then
        ⟨plug (f :: fs) focus, expected + (f :: fs).length, 0⟩
      else
        let step := repairFrame expected actual focus f
        let result := repairContext (expected + 1) step.height step.tree fs
        let cost := match fs with
          | [] => step.cost
          | _ :: _ => repairFrameOpenCost expected actual focus f
        ⟨result.tree, result.height, cost + result.cost⟩

end RotationBST.Arboral.Split.Multiway.Finger
