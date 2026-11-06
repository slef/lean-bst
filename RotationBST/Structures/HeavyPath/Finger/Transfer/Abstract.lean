module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Finger.Transfer.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Transfer.Results
open PopTart PopTart.WeightedTree PopTart.Chocolate

theorem downLeft_trace {p : Pair} {a b : Tree} {oldCharge : ℝ}
    (exposed : p.lower.top = .leaf (Tree.node a b).mirror oldCharge) (lowerCharge upperCharge : ℝ) :
    Pointer.Trace ⟨p.tree, []⟩ ⟨(p.downLeft a b lowerCharge upperCharge).tree, []⟩ p.downLeftCost :=
  RotationBST.HeavyPath.Finger.downLeft_trace exposed lowerCharge upperCharge

theorem downLeft_valid {p : Pair} (valid : p.Valid) (a b : Tree)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    (p.downLeft a b lowerCharge upperCharge).Valid :=
  RotationBST.HeavyPath.Finger.downLeft_valid valid a b lowerNonnegative upperNonnegative

theorem downLeft_amortized {p : Pair} (valid : p.Valid) (a b : Tree)
    (lowerCharge : ℝ) {upperCharge : ℝ} (upperNonnegative : 0 ≤ upperCharge) :
    p.downLeftCost + (p.downLeft a b lowerCharge upperCharge).potential ≤ 26 + p.potential :=
  RotationBST.HeavyPath.Finger.downLeft_amortized valid a b lowerCharge upperNonnegative

theorem downLeft_mass {p : Pair} (valid : p.Valid) {a b : Tree} {oldCharge : ℝ}
    (exposed : p.lower.top = .leaf (Tree.node a b).mirror oldCharge)
    (lowerCharge : ℝ) {upperCharge : ℝ} (upperNonnegative : 0 ≤ upperCharge) :
    (p.downLeft a b lowerCharge upperCharge).mass + oldCharge = p.mass + lowerCharge + upperCharge :=
  RotationBST.HeavyPath.Finger.downLeft_mass valid exposed lowerCharge upperNonnegative

theorem downLeft_root_key {p : Pair} {a b : Tree} {oldCharge : ℝ}
    (exposed : p.lower.top = .leaf (Tree.node a b).mirror oldCharge) (lowerCharge upperCharge : ℝ) :
    (Pointer.Config.mk (p.downLeft a b lowerCharge upperCharge).tree []).key? =
      some (p.lower.decode.tree.mirror.size - b.size - 1) :=
  RotationBST.HeavyPath.Finger.downLeft_root_key exposed lowerCharge upperCharge

theorem flip_tree (p : Pair) : p.flip.tree = p.tree.mirror :=
  RotationBST.HeavyPath.Finger.flip_tree p

theorem flip_mass (p : Pair) : p.flip.mass = p.mass :=
  RotationBST.HeavyPath.Finger.flip_mass p

theorem flip_potential (p : Pair) : p.flip.potential = p.potential :=
  RotationBST.HeavyPath.Finger.flip_potential p

theorem downRight_trace {p : Pair} {a b : Tree} {oldCharge : ℝ}
    (exposed : p.upper.top = .leaf (.node a b) oldCharge) (lowerCharge upperCharge : ℝ) :
    Pointer.Trace ⟨p.tree, []⟩ ⟨(p.downRight a b lowerCharge upperCharge).tree, []⟩ p.downRightCost :=
  RotationBST.HeavyPath.Finger.downRight_trace exposed lowerCharge upperCharge

theorem downRight_valid {p : Pair} (valid : p.Valid) (a b : Tree)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    (p.downRight a b lowerCharge upperCharge).Valid :=
  RotationBST.HeavyPath.Finger.downRight_valid valid a b lowerNonnegative upperNonnegative

theorem downRight_amortized {p : Pair} (valid : p.Valid) (a b : Tree)
    {lowerCharge : ℝ} (upperCharge : ℝ) (lowerNonnegative : 0 ≤ lowerCharge) :
    p.downRightCost + (p.downRight a b lowerCharge upperCharge).potential ≤ 26 + p.potential :=
  RotationBST.HeavyPath.Finger.downRight_amortized valid a b upperCharge lowerNonnegative

theorem downRight_mass {p : Pair} (valid : p.Valid) {a b : Tree} {oldCharge : ℝ}
    (exposed : p.upper.top = .leaf (.node a b) oldCharge)
    {lowerCharge : ℝ} (upperCharge : ℝ) (lowerNonnegative : 0 ≤ lowerCharge) :
    (p.downRight a b lowerCharge upperCharge).mass + oldCharge = p.mass + lowerCharge + upperCharge :=
  RotationBST.HeavyPath.Finger.downRight_mass valid exposed upperCharge lowerNonnegative

theorem downRight_root_key (p : Pair) (a b : Tree) (lowerCharge upperCharge : ℝ) :
    (Pointer.Config.mk (p.downRight a b lowerCharge upperCharge).tree []).key? =
      some (p.lower.decode.tree.mirror.size + a.size + 1) :=
  RotationBST.HeavyPath.Finger.downRight_root_key p a b lowerCharge upperCharge

theorem downLeft_fringe {p : Pair} (valid : p.Valid) {a b : Tree} {oldCharge : ℝ}
    (exposed : p.lower.top = .leaf (Tree.node a b).mirror oldCharge)
    (lowerCharge : ℝ) {upperCharge : ℝ} (upperNonnegative : 0 ≤ upperCharge) :
    ∃ before,
      p.lower.decode.mirror.fringe = before ++ [(.node a b, oldCharge)] ∧
      (p.downLeft a b lowerCharge upperCharge).lower.decode.mirror.fringe = before ++ [(a, lowerCharge)] ∧
      (p.downLeft a b lowerCharge upperCharge).upper.decode.fringe = (b, upperCharge) :: p.upper.decode.fringe :=
  RotationBST.HeavyPath.Finger.downLeft_fringe valid exposed lowerCharge upperNonnegative

theorem downRight_fringe {p : Pair} (valid : p.Valid) {a b : Tree} {oldCharge : ℝ}
    (exposed : p.upper.top = .leaf (.node a b) oldCharge)
    {lowerCharge : ℝ} (upperCharge : ℝ) (lowerNonnegative : 0 ≤ lowerCharge) :
    ∃ after,
      p.upper.decode.fringe = (.node a b, oldCharge) :: after ∧
      (p.downRight a b lowerCharge upperCharge).upper.decode.fringe = (b, upperCharge) :: after ∧
      (p.downRight a b lowerCharge upperCharge).lower.decode.mirror.fringe =
        p.lower.decode.mirror.fringe ++ [(a, lowerCharge)] :=
  RotationBST.HeavyPath.Finger.downRight_fringe valid exposed upperCharge lowerNonnegative

end RotationBST.HeavyPath.Finger.Transfer.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Finger.Transfer.Results`: 15 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Finger.Transfer.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Top.Definitions.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Transfer.Definitions.Abstract]
