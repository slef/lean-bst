module

public import RotationBST.Algorithms.Tango.State.ComponentPath.Defs
public import RotationBST.Algorithms.Tango.State.Context.Fringe.Defs

@[expose] public section
namespace RotationBST.Tango.Context

/-- Compile a nearest-first reference context into an outer-to-inner component
path and the unmarked context inside the final component. -/
def componentAddress : List Frame → List Nat × List Frame
  | [] => ([], [])
  | f :: fs =>
      let (path, inner) := componentAddress fs
      if f.marked then (path ++ [(before (f :: inner)).length], [])
      else (path, f :: inner)

end RotationBST.Tango.Context
