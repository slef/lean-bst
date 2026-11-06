module

public import RotationBST.Algorithms.Tango.Algorithm.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Algorithm.Request.Abstract
public import RotationBST.Algorithms.Tango.State.Preferences.Algorithm.Defs

@[expose] public section
namespace RotationBST.Tango.Initialization
open MarkedTree Context

/-- First joins retain their actual target component size; empty children
require no rotations and make no potential change. -/
noncomputable def componentCharge (fs : List Frame) (l r : MarkedTree) (next : Bool) : ℝ :=
  if (if next then l else r) = .nil then 0
  else 8 * Real.logb 2 (plug fs (.node l r (!next) next)).region.size + 2

/-- Charge the compiled reference update according to its current marks.
This inspects the reference state, not a potentially inconsistent log label. -/
noncomputable def updateCharge (reference : MarkedTree) (key : Nat) (next : Bool) : ℝ :=
  match reference.locateKey key with
  | some (.node l r cl cr, fs) =>
      if cl && cr then componentCharge (componentAddress fs).2 l r next
      else 14 * Real.logb 2 (height reference.tree) + 4
  | _ => 0

/-- Advance the actual reference marks between charged updates. -/
noncomputable def logCharge : MarkedTree → List PreferenceUpdate → ℝ
  | _, [] => 0
  | reference, u :: us => updateCharge reference u.key u.next +
      logCharge (reference.setPreference u.key u.next) us

/-- Preference maintenance followed by the final root-component access. -/
noncomputable def requestCharge (reference : Tree) (past : List Nat) (x : Nat) : ℝ :=
  logCharge (canonical reference 0 past) (preferenceUpdates reference 0 past x) +
    (3 * Real.logb 2 (height reference) + 1)

noncomputable def sequenceCharge (reference : Tree) : List Nat → List Nat → ℝ
  | _, [] => 0
  | past, x :: xs => requestCharge reference past x + sequenceCharge reference (past ++ [x]) xs

/-- Reference nodes with no preference set yet, including empty-child marks. -/
def virginCount : MarkedTree → Nat
  | .nil => 0
  | .node l r cl cr => (if cl && cr then 1 else 0) + virginCount l + virginCount r

def firstAt (reference : MarkedTree) (key : Nat) : Bool :=
  match reference.locateKey key with
  | some (.node _ _ cl cr, _) => cl && cr
  | _ => false

def firstCount : MarkedTree → List PreferenceUpdate → Nat
  | _, [] => 0
  | reference, u :: us => (if firstAt reference u.key then 1 else 0) +
      firstCount (reference.setPreference u.key u.next) us

def laterCount : MarkedTree → List PreferenceUpdate → Nat
  | _, [] => 0
  | reference, u :: us => (if firstAt reference u.key then 0 else 1) +
      laterCount (reference.setPreference u.key u.next) us

/-- Keep only initialization charges, classified from the evolving marks. -/
noncomputable def firstLogCharge : MarkedTree → List PreferenceUpdate → ℝ
  | _, [] => 0
  | reference, u :: us => (if firstAt reference u.key then updateCharge reference u.key u.next else 0) +
      firstLogCharge (reference.setPreference u.key u.next) us

end RotationBST.Tango.Initialization
