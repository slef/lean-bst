module

public import RotationBST.Algorithms.Tango.State.Context.Lookup.Defs
public import RotationBST.Algorithms.Tango.State.Nesting.Defs

@[expose] public section
namespace RotationBST.Tango

/-- Replace one component signature along a path of fringe indices. -/
def ComponentNesting.replaceAt : ComponentNesting → List Nat → ComponentNesting → ComponentNesting
  | _, [], target => target
  | source, i :: rest, target =>
      match source.fringe[i]? with
      | none => source
      | some child => .branch (source.fringe.set i (child.replaceAt rest target))

namespace MarkedTree

/-- Follow a path of fringe indices to a nested component. The empty path
selects the root component. -/
def componentAt : MarkedTree → List Nat → Option MarkedTree
  | s, [] => some s
  | s, i :: rest => s.fringe[i]?.bind fun child => child.componentAt rest

/-- Execute a local edit in a nested component, reassembling each enclosing
context. This computes the complete marked state and rotation count. -/
def editAt (s : MarkedTree) (path : List Nat) (edit : MarkedTree → MarkedTree × Nat) : MarkedTree × Nat :=
  match path with
  | [] => edit s
  | i :: rest => Context.editFringe s i (fun child => child.editAt rest edit)

end MarkedTree
end RotationBST.Tango
