module

public import RotationBST.Algorithms.Tango.Preferences.Abstract

@[expose] public section
namespace RotationBST.Tango

/-- One changed preference at an absolute reference key. `none` is its first
setting; an existing equal preference produces no log entry. -/
structure PreferenceUpdate where
  key : Nat
  previous : Option Bool
  next : Bool
  deriving DecidableEq, Repr

/-- Changes for one request, in reference-root-to-request order. Requests and
history use local ranks; `lo` translates the recorded node keys to global ranks. -/
def preferenceUpdates : Tree → Nat → List Nat → Nat → List PreferenceUpdate
  | .nil, _, _, _ => []
  | .node l r, lo, past, x =>
      if x < l.size + 1 + r.size then
        let previous := (regions l.size (l.size + 1 + r.size) past).getLast?
        let next := decide (x ≤ l.size)
        (if previous = some next then [] else [⟨lo + l.size, previous, next⟩]) ++
          if x < l.size then preferenceUpdates l lo (leftRequests l.size past) x
          else if x = l.size then []
          else preferenceUpdates r (lo + l.size + 1) (rightRequests l.size past) (x - l.size - 1)
      else []

/-- The causally generated preference-change log for a request sequence. -/
def preferenceLog (t : Tree) : List Nat → List Nat → List PreferenceUpdate
  | _, [] => []
  | past, x :: xs => preferenceUpdates t 0 past x ++ preferenceLog t (past ++ [x]) xs

end RotationBST.Tango
