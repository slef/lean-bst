module

public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Partial.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded

/-- Remaining splitting budget: node reserves plus a size/logarithm allowance.
It is attached to the interval once and passed to its descendants. -/
def intervalCredit (input : Option State) : Nat :=
  14 * intervalNodes input +
    3000 * (2 * (intervalTree input).size - Nat.log2 ((intervalTree input).size + 1))

def Partitioned.credit : Partitioned → Nat
  | .leaf input => intervalCredit input
  | .branch l r => l.credit + r.credit

/-- Refine one retained interval, possibly below already exposed separators. -/
inductive Refine : Partitioned → Partitioned → Nat → Prop where
  | leaf (plan : Plan) (input : Option State) (applicable : plan.Applicable input) :
      Refine (.leaf input) (runPlan plan input).1 (runPlan plan input).2
  | left {s t r : Partitioned} {cost : Nat} : Refine s t cost → Refine (.branch s r) (.branch t r) cost
  | right {l s t : Partitioned} {cost : Nat} : Refine s t cost → Refine (.branch l s) (.branch l t) cost

/-- Split decisions may arrive in any order and over arbitrarily many rows. -/
inductive Refinement : Partitioned → Partitioned → Nat → Prop where
  | refl {state : Partitioned} : Refinement state state 0
  | step {s t u : Partitioned} {first rest : Nat} :
      Refine s t first → Refinement t u rest → Refinement s u (first + rest)

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded
