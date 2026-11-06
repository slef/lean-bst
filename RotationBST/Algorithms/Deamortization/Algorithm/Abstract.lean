module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Deamortization.Algorithm.AbstractBridge

@[expose] public section

/-! Abstract deamortization for every certified online rotation algorithm.
One causal program has linear setup, constant-factor total cost, and logarithmic
worst-case responses. Private computation and storage are not bounded here. -/
namespace RotationBST.Deamortization.Algorithm.Results

theorem implementation_exists (source : RotationBST.Algorithm) (saved : Tree) (nonempty : saved ≠ .nil) :
    Nonempty (Implementation source saved) :=
  RotationBST.Deamortization.Algorithm.implementation_exists source saved nonempty

theorem total_bound {source : RotationBST.Algorithm} {saved : Tree}
    (d : Implementation source saved) {keys : List Nat} (valid : ∀ x ∈ keys, x < saved.size)
    {out : Scheduler.Output} (completed : d.program keys = some out) :
    d.startup + out.costs.sum ≤ 16 * saved.size + 79360 * source.totalCost saved keys :=
  RotationBST.Deamortization.Algorithm.Implementation.total_bound d valid completed

theorem transfer {source : RotationBST.Algorithm} {saved : Tree}
    (d : Implementation source saved) {keys : List Nat} (valid : ∀ x ∈ keys, x < saved.size)
    {out : Scheduler.Output} (completed : d.program keys = some out) {bound : ℝ}
    (sourceBound : (source.totalCost saved keys : ℝ) ≤ bound) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 79360 * bound :=
  RotationBST.Deamortization.Algorithm.Implementation.transfer d valid completed sourceBound

theorem dynamic_optimal (source : RotationBST.Algorithm) (optimal : TotallyDynamicallyOptimal source) :
    ∃ C D : Nat, ∀ saved : Tree, saved ≠ .nil →
      ∃ d : Implementation source saved, ∀ (xs : List Nat) (finish : Tree) (k : Nat),
        RotationBST.Execution saved xs finish k → ∀ out,
          d.program xs = some out → d.startup + out.costs.sum ≤ C * (xs.length + k) + D * saved.size :=
  RotationBST.Deamortization.Algorithm.dynamic_optimal source optimal

end RotationBST.Deamortization.Algorithm.Results

/-- info: abstract audit passed for `RotationBST.Deamortization.Algorithm.Results`: 4 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Deamortization.Algorithm.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Multifinger.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Algorithms.Deamortization.Scheduler.Definitions.Abstract,
  RotationBST.Algorithms.Deamortization.Algorithm.Definitions.Abstract]
