module

public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.Red
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Unaccessed
open Items Reference

/-- Searches on both sides of an item cover its distance to their LCA:
at the first separating branch, the opposite search exposes the item's child. -/
theorem enclosing_blue (t : Tree) (lo a x b : Nat) (ax : a < x) (xb : x < b) :
    Distance.toLCA t lo x a b ≤ max (blue t lo a x) (blue t lo b x) := by
  induction t generalizing lo with
  | nil => simp [Distance.toLCA, Distance.depth, Distance.lcaDepth, blue]
  | node l r il ir =>
    by_cases left : b < lo + leaves l
    · have aLeft : a < lo + leaves l := by omega
      have xLeft : x < lo + leaves l := by omega
      simpa only [Distance.toLCA, Distance.depth, Distance.lcaDepth, blue,
        left, aLeft, xLeft,
        and_self, ite_true, Nat.add_sub_add_right] using il lo
    · by_cases right : lo + leaves l ≤ a
      · have bRight : lo + leaves l ≤ b := by omega
        have xRight : ¬ x < lo + leaves l := by omega
        have aRight : ¬ a < lo + leaves l := by omega
        simpa only [Distance.toLCA, Distance.depth, Distance.lcaDepth, blue,
          left, aRight, xRight,
          false_and, ite_false, right, bRight, and_self, ite_true,
          Nat.add_sub_add_right] using ir (lo + leaves l)
      · have aLeft : a < lo + leaves l := by omega
        have bRight : lo + leaves l ≤ b := by omega
        by_cases xLeft : x < lo + leaves l
        · simp only [Distance.toLCA, Distance.depth, Distance.lcaDepth, blue,
            aLeft, left, right, xLeft, and_false, false_and, ite_false,
            ite_true, Nat.sub_zero]
          exact le_max_right _ _
        · simp only [Distance.toLCA, Distance.depth, Distance.lcaDepth, blue,
            aLeft, left, right, xLeft, and_false, false_and, ite_false,
            ite_true, Nat.sub_zero]
          exact le_max_left _ _

end RotationBST.Geometric.GreedyASS.Potential.Unaccessed
