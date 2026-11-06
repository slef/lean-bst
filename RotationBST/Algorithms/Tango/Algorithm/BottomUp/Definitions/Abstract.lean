module

public import RotationBST.Algorithms.Tango.Algorithm.Request.Abstract
public import RotationBST.Algorithms.Tango.Algorithm.Initialization.Definitions.Abstract

@[expose] public section
namespace RotationBST.Tango.BottomUp
open MarkedTree

/-- Compile one request's distinct reference changes from the deepest node
upward, then access the key in the resulting root component. -/
def serve (s : MarkedTree) (reference : Tree) (past : List Nat) (x : Nat) : MarkedTree × Nat :=
  let updated := s.updatePreferences (canonical reference 0 past) (preferenceUpdates reference 0 past x).reverse
  let accessed := updated.1.splayRoot (Region.index updated.1.region 0 x)
  (accessed.1, updated.2 + accessed.2)

/-- Reverse within each request only; the request sequence remains causal. -/
def log (reference : Tree) : List Nat → List Nat → List PreferenceUpdate
  | _, [] => []
  | past, x :: xs => (preferenceUpdates reference 0 past x).reverse ++ log reference (past ++ [x]) xs

/-- The refined charge uses the actual intermediate reference components in
bottom-up order, not the components of the top-down execution. -/
noncomputable def requestCharge (reference : Tree) (past : List Nat) (x : Nat) : ℝ :=
  Initialization.logCharge (canonical reference 0 past) (preferenceUpdates reference 0 past x).reverse +
    (3 * Real.logb 2 (height reference) + 1)

noncomputable def sequenceCharge (reference : Tree) : List Nat → List Nat → ℝ
  | _, [] => 0
  | past, x :: xs => requestCharge reference past x + sequenceCharge reference (past ++ [x]) xs

end RotationBST.Tango.BottomUp
