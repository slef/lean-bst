module

public import RotationBST.Algorithms.Tango.Preferences.Updates.Abstract
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace RotationBST.Tango.Initialization
open Wilber

/-- The accumulated charge of reference nodes observed by the history. The
weight belongs to the reference key, independently of when it is first seen. -/
def observedCharge : Tree → Nat → List Nat → (Nat → ℝ) → ℝ
  | .nil, _, _, _ => 0
  | .node l r, lo, past, w =>
      (if regions l.size (l.size + 1 + r.size) past = [] then 0 else w (lo + l.size)) +
      observedCharge l lo (leftRequests l.size past) w +
      observedCharge r (lo + l.size + 1) (rightRequests l.size past) w

/-- Total available initialization credit, one weight per reference node. -/
def allowance : Tree → Nat → (Nat → ℝ) → ℝ
  | .nil, _, _ => 0
  | .node l r, lo, w => w (lo + l.size) + allowance l lo w + allowance r (lo + l.size + 1) w

/-- Charge only actual first-setting events in the executable update log. -/
def firstCharge (updates : List PreferenceUpdate) (w : Nat → ℝ) : ℝ :=
  ((updates.filter fun e => e.previous.isNone).map fun e => w e.key).sum

end RotationBST.Tango.Initialization
