module

import RotationBST.Audit.Check
public import RotationBST.Models.RealWorld.AbstractBridge

@[expose] public section
namespace RotationBST.RealWorld.Results

theorem physical {w f r l : Nat} {p : Machine f r l}
    {s t : State w f r l} {time cost : Nat} (h : Run p s t time cost) :
    Pointer.Trace s.cursor.erase t.cursor.erase cost := run_physical h

theorem bst_cost {w f r l : Nat} {p : Machine f r l}
    {s t : State w f r l} {time cost : Nat} (h : Run p s t time cost) :
    cost ≤ time := cost_le_time h

theorem causal {w f r l : Nat} {p : Machine f r l}
    {s t u : State w f r l} {xs : List (BitVec w)} {a b c d : Nat}
    (h : Execution p s xs t a b) (k : Execution p s xs u c d) :
    t = u ∧ a = c ∧ b = d := execution_unique h k

theorem append {w f r l : Nat} {p : Machine f r l}
    {s t u : State w f r l} {xs ys : List (BitVec w)} {a b c d : Nat}
    (h : Execution p s xs t a b) (k : Execution p t ys u c d) :
    Execution p s (xs ++ ys) u (a + c) (b + d) := execution_append h k

end RotationBST.RealWorld.Results

#check_bst_abstract RotationBST.RealWorld.Results allowing [
  RotationBST.Models.RealWorld.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Definitions.Abstract,
  RotationBST.Models.Labelled.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Rotation.Abstract]
