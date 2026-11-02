module

public import RotationBST.Tango.State.Preferences.Lookup.Abstract
public import RotationBST.Tango.State.Preferences.Abstract
public import RotationBST.Tango.State.ComponentPath.Address.Abstract
public import RotationBST.Tango.State.Nesting.Edits.Path.Algorithm.Abstract

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Set a reference node's preference inside its auxiliary component. Existing
preferences require at most one cut and one join; a first preference only joins. -/
def setMarksInPath (s : MarkedTree) (fs : List Context.Frame) (l r : MarkedTree)
    (cl cr next : Bool) : MarkedTree × Nat :=
  if cl == !next && cr == next then (s, 0)
  else if cl && cr then
    if next then s.unmarkInPath fs (.left r true true)
    else s.unmarkInPath fs (.right l true true)
  else s.switchInPath fs l r (!cl)

/-- Compile one reference-key preference update into rotations of the actual
marked BST. The address and interval boundaries are computed from the reference. -/
def updatePreference (s reference : MarkedTree) (key : Nat) (next : Bool) : MarkedTree × Nat :=
  match reference.locateKey key with
  | some (.node l r cl cr, fs) =>
      let (path, inner) := Context.componentAddress fs
      s.editAt path (fun actual => actual.setMarksInPath inner l r cl cr next)
  | _ => (s, 0)

/-- Execute an update log while advancing the reference marking after every edit. -/
def updatePreferences (s reference : MarkedTree) : List PreferenceUpdate → MarkedTree × Nat
  | [] => (s, 0)
  | u :: us =>
      let first := s.updatePreference reference u.key u.next
      let rest := updatePreferences first.1 (reference.setPreference u.key u.next) us
      (rest.1, first.2 + rest.2)

end RotationBST.Tango.MarkedTree
