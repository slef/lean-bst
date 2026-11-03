module

public import RotationBST.Structures.SplitTree.Finger.Maximum.Partition.Accounting
public import RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Context.HeightLoss

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

/-- The retained side loses at most the height of the located interval. -/
theorem splitFromMaximum_height_gap {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size) :
    h ≤ (splitFromMaximum t distance).left.height + Nat.log2 (distance + 1) + 1 := by
  have interval := locateMaximum_balance valid distance
  have contains := maximumLocal_rank t distance existsKey
  have pieces := (Multiway.Partition.run_spec interval.1 ((locateMaximum t distance).focus.size - 1 - distance) contains).1
  have heights := Multiway.Partition.run_height interval.1 ((locateMaximum t distance).focus.size - 1 - distance) contains
  have lower := maximumRepairContext_height_lower (locateMaximum t distance).outer pieces.1 interval.2
    (fun f member => rightSpine_frames t f (List.mem_of_mem_drop member)) heights.1
  have localHeight := locateMaximum_height valid distance
  have length := (rightSpine_balanced valid).2
  have enough := ascend_length (rightSpine t) .nil distance
  have total : (locateMaximum t distance).height + (locateMaximum t distance).outer.length = h := by
    simp only [locateMaximum, List.length_drop]
    omega
  change _ ≤ (maximumRepairLocated t distance).height at lower
  change h ≤ (maximumRepairLocated t distance).height + _ + 1
  omega

/-- If splitting lowers the enclosing side's height, its removed-node reserve
pays for that side's entire old height, up to logarithmic local work. -/
theorem splitFromMaximum_height_loss {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size)
    (lost : (maximumRepairLocated t distance).height < h) :
    (splitFromMaximum t distance).left.tree.nodes + (splitFromMaximum t distance).right.tree.nodes + h ≤
      t.nodes + 30 * (Nat.log2 (distance + 1) + 1) + 4 := by
  have interval := locateMaximum_balance valid distance
  have contains := maximumLocal_rank t distance existsKey
  have pieces := (Multiway.Partition.run_spec interval.1 ((locateMaximum t distance).focus.size - 1 - distance) contains).1
  have heights := Multiway.Partition.run_height interval.1 ((locateMaximum t distance).focus.size - 1 - distance) contains
  have allocation := Multiway.Partition.run_allocation (locateMaximum t distance).height (locateMaximum t distance).focus ((locateMaximum t distance).focus.size - 1 - distance) contains
  have localCost := Multiway.Partition.run_cost interval.1 ((locateMaximum t distance).focus.size - 1 - distance) contains
  have localHeight := locateMaximum_height valid distance
  have length := (rightSpine_balanced valid).2
  have enough := ascend_length (rightSpine t) .nil distance
  have total : (locateMaximum t distance).height + (locateMaximum t distance).outer.length = h := by
    simp only [locateMaximum, List.length_drop]
    omega
  have repair := maximumRepairContext_height_loss (locateMaximum t distance).outer pieces.1 interval.2
    (fun f member => rightSpine_frames t f (List.mem_of_mem_drop member)) heights.1 (by
      change (maximumRepairLocated t distance).height < _
      rwa [total])
  have original := plug_nodes (locateMaximum t distance).outer (locateMaximum t distance).focus
  rw [locateMaximum_reconstruct] at original
  have remaining := plug_nodes (locateMaximum t distance).outer
    (Multiway.Partition.run (locateMaximum t distance).height (locateMaximum t distance).focus ((locateMaximum t distance).focus.size - 1 - distance)).left.tree
  change (maximumRepairLocated t distance).tree.nodes + _ ≤ _ at repair
  simp only [splitFromMaximum]
  omega

end RotationBST.Arboral.Split.Multiway.Finger
