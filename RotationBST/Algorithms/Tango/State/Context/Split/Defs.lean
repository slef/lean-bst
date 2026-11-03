module

public import RotationBST.Algorithms.Tango.State.Context.Defs

@[expose] public section
namespace RotationBST.Tango.Context

/-- Split nearest-first ancestors into the current component's unmarked path
and the outer context beginning at its first marked boundary. -/
def splitComponent : List Frame → List Frame × List Frame
  | [] => ([], [])
  | f :: fs =>
      if f.marked then ([], f :: fs)
      else let (inner, outer) := splitComponent fs; (f :: inner, outer)

end RotationBST.Tango.Context
