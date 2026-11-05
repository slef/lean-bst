module

import RotationBST.Audit.Check
public import RotationBST.Models.LinkedSearch.AbstractBridge

@[expose] public section
namespace RotationBST.LinkedSearch.Results

theorem shape {ι : Type} (target : Nat → ι) (t : LabelledTree Nat) :
    (attach target t).erase = t.erase := attach_erase target t

/-- Links change the returned payload but do not change the search path. -/
theorem search {ι : Type} (target : Nat → ι) (t : LabelledTree Nat) (x : Nat) :
    lookup (attach target t) x =
      (if (LabelledTree.lookup t x).1 then some (target x) else none, (LabelledTree.lookup t x).2) :=
  attach_lookup target t x

theorem traversal {ι : Type} (t : LabelledTree (Entry ι)) (x : Nat) :
    Search t x (lookup t x).1 (lookup t x).2 := lookup_search t x

/-- The executable request follows the returned stored link, charging its
local search, any fallback search, and the link traversals. -/
theorem query {ι : Type} (s : Store ι) (current next : ι) (x : Nat)
    (success : (request s current x).1 = some next) :
    Request s current x next (request s current x).2 := request_correct s current next x success

end RotationBST.LinkedSearch.Results

/-- info: abstract audit passed for `RotationBST.LinkedSearch.Results`: 4 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.LinkedSearch.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Labelled.Search.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Models.LinkedSearch.Definitions.Abstract]
