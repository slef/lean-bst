module

public import RotationBST.Structures.SplitTree.Finger.Maximum.Partition.Proofs
public import RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Context.Accounting
public import RotationBST.Structures.SplitTree.Multiway.Partition.Allocation

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger
open Context

/-- The complete maximum-finger split has logarithmic amortized distance cost.
Both output node reserves are included, so the accounting composes across later
splits of either result. Choosing the nearer endpoint is a separate obligation. -/
theorem splitFromMaximum_credit {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size) :
    (splitFromMaximum t distance).cost +
      2 * ((splitFromMaximum t distance).left.tree.nodes + (splitFromMaximum t distance).right.tree.nodes) ≤
      2 * t.nodes + 85 * (Nat.log2 (distance + 1) + 1) + 29 := by
  have interval := locateMaximum_balance valid distance
  have contains := maximumLocal_rank t distance existsKey
  have pieces := (Multiway.Partition.run_spec interval.1 ((locateMaximum t distance).focus.size - 1 - distance) contains).1
  have heights := Multiway.Partition.run_height interval.1 ((locateMaximum t distance).focus.size - 1 - distance) contains
  have allocation := Multiway.Partition.run_allocation (locateMaximum t distance).height (locateMaximum t distance).focus ((locateMaximum t distance).focus.size - 1 - distance) contains
  have localCost := Multiway.Partition.run_cost interval.1 ((locateMaximum t distance).focus.size - 1 - distance) contains
  have exposure := (splitLocatedMaximum_spec valid distance existsKey).2
  have localHeight := locateMaximum_height valid distance
  have repair := maximumRepairContext_credit (locateMaximum t distance).outer pieces.1 interval.2
    (fun f member => rightSpine_frames t f (List.mem_of_mem_drop member)) heights.1
  have original := plug_nodes (locateMaximum t distance).outer (locateMaximum t distance).focus
  rw [locateMaximum_reconstruct] at original
  have remaining := plug_nodes (locateMaximum t distance).outer
    (Multiway.Partition.run (locateMaximum t distance).height (locateMaximum t distance).focus ((locateMaximum t distance).focus.size - 1 - distance)).left.tree
  change (maximumRepairLocated t distance).cost + 2 * (maximumRepairLocated t distance).tree.nodes ≤ _ at repair
  simp only [splitFromMaximum]
  omega

end RotationBST.Geometric.Split.Multiway.Finger
