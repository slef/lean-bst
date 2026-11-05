module

public import RotationBST.Bounds.StaticTree.Definitions.Abstract

@[expose] public section
namespace RotationBST.WeightedSearch

/-- Locate the key containing a given unit of cumulative integer weight.
Zero-weight keys are skipped. The specification requires `target < sum`. -/
def locate : List Nat → Nat → Nat
  | [], _ => 0
  | w :: ws, target => if target < w then 0 else 1 + locate ws (target - w)

/-- Select a weighted median. An all-zero interval selects its first key;
positive-weight depth guarantees do not depend on this tie convention. -/
def pivot (weights : List Nat) : Nat :=
  if weights.sum = 0 then 0 else locate weights (weights.sum / 2)

/-- Weighted-median recursion with explicit fuel. `build` supplies enough fuel
to retain every key, including keys of weight zero. -/
def buildFuel : Nat → List Nat → Tree
  | 0, _ => .nil
  | _ + 1, [] => .nil
  | fuel + 1, w :: ws =>
      let weights := w :: ws
      let p := pivot weights
      .node (buildFuel fuel (weights.take p)) (buildFuel fuel (weights.drop (p + 1)))

/-- A static BST whose inorder ranks are the positions in the weight list. -/
def build (weights : List Nat) : Tree := buildFuel weights.length weights

/-- Add a uniform baseline to the weighted frequencies. The extra unit makes
all entries positive even when the entire observed row is zero. -/
def regularize (weights : List Nat) : List Nat :=
  weights.map fun w => weights.length * w + weights.sum + 1

/-- A frequency-biased tree with logarithmic worst-case depth for every key,
including those not yet observed. -/
def balancedBuild (weights : List Nat) : Tree := build (regularize weights)

end RotationBST.WeightedSearch
