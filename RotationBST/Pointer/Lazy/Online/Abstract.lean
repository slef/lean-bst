module

import RotationBST.AbstractAudit.Check
public import RotationBST.Pointer.Lazy.Online.AbstractBridge

@[expose] public section

/-! A causal transformer from every certified rotation-model algorithm to the
single-pointer model. Its implementation is in `Algorithm/Abstract`: each step
uses only the current request, the past, and a state recording deferred work.
Classical choice is used for uncharged planning. -/
namespace RotationBST.Pointer.Lazy.Online.Results

/-- The chosen pointer strategy serves every valid request, retains an explicit
final deferred suffix, and has a uniform constant-factor cost bound. -/
theorem simulation (a : RotationBST.Algorithm) (past : List Nat) (t : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < t.size) :
    Pointer.Execution t xs (run a past (initial t) xs).1.current (run a past (initial t) xs).2 ∧
    Rotations (run a past (initial t) xs).1.current (a.runFrom past t xs).1
      (run a past (initial t) xs).1.pending ∧
    (run a past (initial t) xs).2 + 32 * (run a past (initial t) xs).1.pending ≤
      32 * (a.runFrom past t xs).2 + 17 * xs.length :=
  from_initial a past t xs valid

/-- Appending requests leaves the prefix computation unchanged. -/
theorem prefix_composition (a : RotationBST.Algorithm) (past : List Nat) (s : State) (xs ys : List Nat) :
    run a past s (xs ++ ys) =
      let first := run a past s xs
      let rest := run a (past ++ xs) first.1 ys
      (rest.1, first.2 + rest.2) :=
  run_append a past s xs ys

/-- Working-set guarantees proved on shapes transfer to the chosen causal
pointer implementation, with uniform constants. -/
theorem workingSet (a : RotationBST.Algorithm) (bound : HasWorkingSetBound a) :
    ∃ C D : Nat, ∀ t xs, (∀ x ∈ xs, x < t.size) →
      (run a [] (initial t) xs).2 ≤ C * workingSetSum t.size [] xs +
        D * t.size * (1 + t.size.log2) :=
  workingSet_transfer a bound

/-- Dynamic optimality, if established in the normalized rotation model,
transfers to comparison with every offline pointer execution. -/
theorem dynamicOptimality (a : RotationBST.Algorithm) (optimal : TotallyDynamicallyOptimal a) :
    ∃ C D : Nat, ∀ t xs u k, Pointer.Execution t xs u k →
      (run a [] (initial t) xs).2 ≤ C * k + D * t.size :=
  dynamic_transfer a optimal

end RotationBST.Pointer.Lazy.Online.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
#check_bst_abstract RotationBST.Pointer.Lazy.Online.Results allowing [
  RotationBST.Model.Abstract,
  RotationBST.Online.Abstract, RotationBST.WorkingSet.Abstract,
  RotationBST.Pointer.Machine.Abstract,
  RotationBST.Pointer.Lazy.Online.Definitions.Abstract,
  RotationBST.Pointer.Lazy.Online.Algorithm.Abstract]
