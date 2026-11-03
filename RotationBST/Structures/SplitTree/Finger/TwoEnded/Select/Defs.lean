module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Partial.Defs
public import Mathlib.Data.Finset.Sort

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded

/-- Select increasing absolute ranks using only this row's choices. Intervals
between consecutive chosen ranks are retained without further splitting. -/
def selectionPlan : Nat → List Nat → Plan
  | _, [] => .stop
  | offset, key :: keys => .branch (key - offset) .stop (selectionPlan (key + 1) keys)

/-- Absolute ranks of exposed separators; retained interval keys are excluded. -/
def Partitioned.keys : Partitioned → Nat → List Nat
  | .leaf _, _ => []
  | .branch l r, offset => l.keys offset ++
      (offset + l.tree.size) :: r.keys (offset + l.tree.size + 1)

/-- Select a finite set of current supernode ranks. No future row is used. -/
def selectKeys (input : Option State) (keys : Finset Nat) : Partitioned × Nat :=
  runPlan (selectionPlan 0 (keys.sort (· ≤ ·))) input

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded
