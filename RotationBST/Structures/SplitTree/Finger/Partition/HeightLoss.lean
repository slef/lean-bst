module

public import RotationBST.Structures.SplitTree.Finger.Partition.Accounting
public import RotationBST.Structures.SplitTree.Finger.Repair.Context.HeightLoss

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger
open Context

/-- The retained side loses at most the height of the located interval. -/
theorem splitFromMinimum_height_gap {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    h ≤ (splitFromMinimum t rank).right.height + Nat.log2 (rank + 1) + 1 := by
  have interval := locate_balance valid rank
  have contains := locate_contains t rank existsKey
  have pieces := (Multiway.Partition.run_spec interval.1 rank contains).1
  have heights := Multiway.Partition.run_height interval.1 rank contains
  have lower := repairContext_height_lower (locate t rank).outer pieces.2 interval.2
    (fun f member => leftSpine_frames t f (List.mem_of_mem_drop member)) heights.2
  have localHeight := locate_height valid rank
  have length := (leftSpine_balanced valid).2
  have enough := ascend_length (leftSpine t) .nil rank
  change searchLevels t rank ≤ (leftSpine t).length at enough
  have total : (locate t rank).height + (locate t rank).outer.length = h := by
    simp only [locate, List.length_drop]
    omega
  change _ ≤ (repairLocated t rank).height at lower
  change h ≤ (repairLocated t rank).height + _ + 1
  omega

/-- If splitting lowers the enclosing side's height, its removed-node reserve
pays for that side's entire old height, up to logarithmic local work. -/
theorem splitFromMinimum_height_loss {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size)
    (lost : (repairLocated t rank).height < h) :
    (splitFromMinimum t rank).left.tree.nodes + (splitFromMinimum t rank).right.tree.nodes + h ≤
      t.nodes + 30 * (Nat.log2 (rank + 1) + 1) + 4 := by
  have interval := locate_balance valid rank
  have contains := locate_contains t rank existsKey
  have pieces := (Multiway.Partition.run_spec interval.1 rank contains).1
  have heights := Multiway.Partition.run_height interval.1 rank contains
  have allocation := Multiway.Partition.run_allocation (locate t rank).height (locate t rank).focus rank contains
  have localCost := Multiway.Partition.run_cost interval.1 rank contains
  have localHeight := locate_height valid rank
  have length := (leftSpine_balanced valid).2
  have enough := ascend_length (leftSpine t) .nil rank
  change searchLevels t rank ≤ (leftSpine t).length at enough
  have total : (locate t rank).height + (locate t rank).outer.length = h := by
    simp only [locate, List.length_drop]
    omega
  have repair := repairContext_height_loss (locate t rank).outer pieces.2 interval.2
    (fun f member => leftSpine_frames t f (List.mem_of_mem_drop member)) heights.2 (by
      change (repairLocated t rank).height < _
      rwa [total])
  have original := plug_nodes (locate t rank).outer (locate t rank).focus
  rw [locate_reconstruct] at original
  have remaining := plug_nodes (locate t rank).outer
    (Multiway.Partition.run (locate t rank).height (locate t rank).focus rank).right.tree
  change (repairLocated t rank).tree.nodes + _ ≤ _ at repair
  simp only [splitFromMinimum]
  omega

end RotationBST.SplitTree.Multiway.Finger
