module

public import RotationBST.Structures.SplitTree.Finger.Partition.Proofs
public import RotationBST.Structures.SplitTree.Finger.Repair.Context.Accounting
public import RotationBST.Structures.SplitTree.Multiway.Partition.Allocation

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger
open Context

/-- The complete minimum-finger split has logarithmic amortized rank cost.
Both output node reserves are included, so the accounting composes across later
splits of either result. Choosing the nearer endpoint is a separate obligation. -/
theorem splitFromMinimum_credit {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    (splitFromMinimum t rank).cost +
      2 * ((splitFromMinimum t rank).left.tree.nodes + (splitFromMinimum t rank).right.tree.nodes) ≤
      2 * t.nodes + 85 * (Nat.log2 (rank + 1) + 1) + 29 := by
  have interval := locate_balance valid rank
  have contains := locate_contains t rank existsKey
  have pieces := (Multiway.Partition.run_spec interval.1 rank contains).1
  have heights := Multiway.Partition.run_height interval.1 rank contains
  have allocation := Multiway.Partition.run_allocation (locate t rank).height (locate t rank).focus rank contains
  have localCost := Multiway.Partition.run_cost interval.1 rank contains
  have exposure := (splitLocated_spec valid rank existsKey).2
  have localHeight := locate_height valid rank
  have repair := repairContext_credit (locate t rank).outer pieces.2 interval.2
    (fun f member => leftSpine_frames t f (List.mem_of_mem_drop member)) heights.2
  have original := plug_nodes (locate t rank).outer (locate t rank).focus
  rw [locate_reconstruct] at original
  have remaining := plug_nodes (locate t rank).outer
    (Multiway.Partition.run (locate t rank).height (locate t rank).focus rank).right.tree
  change (repairLocated t rank).cost + 2 * (repairLocated t rank).tree.nodes ≤ _ at repair
  simp only [splitFromMinimum]
  omega

end RotationBST.Geometric.Split.Multiway.Finger
