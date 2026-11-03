module

public import RotationBST.Algorithms.Tango.State.Preferences.Algorithm.Defs
public import RotationBST.Algorithms.Tango.Preferences.Updates.Abstract

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Serve a request by compiling the reference preference changes, then splaying
the requested key in the resulting root component. Only the past is inspected. -/
def serve (s : MarkedTree) (reference : Tree) (past : List Nat) (x : Nat) : MarkedTree × Nat :=
  let updated := s.updatePreferences (canonical reference 0 past) (preferenceUpdates reference 0 past x)
  let accessed := updated.1.splayRoot (Geometric.Region.index updated.1.region 0 x)
  (accessed.1, updated.2 + accessed.2)

end RotationBST.Tango.MarkedTree
