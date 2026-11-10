module

import RotationBST.Audit.Check
public import RotationBST.Classical.RankBalanced.Insertion.AbstractBridge

@[expose] public section

/-! Insertion into WAVL and AVL trees. `Definitions/Abstract` gives the leaf
insertion `LabelledTree.insertAt` (a leaf of rank 0), the rebalancing `fixLeft`/`fixRight`, `insert` (tree,
rotations, rank changes), `insertAll` and `insertEdits`. Costs are those of the
dictionary model (`Models/Dictionary`); rank changes are its data edits. -/
namespace RotationBST.Classical.RankBalanced.Results

/-- Insertion is a dictionary step: `1 + depth` of the new leaf plus the
rotations, and one data edit per rank change. -/
theorem insert_step (t : RankedTree) (g : Nat) (hg : g ≤ t.erase.size) :
    Dictionary.Step t (.insert g) (insert t g).1
      ((t.insertAt g 0).erase.depth g + 1 + (insert t g).2.1) (insert t g).2.2 :=
  RankBalanced.insert_step t g hg

theorem insert_size (t : RankedTree) (g : Nat) : (insert t g).1.erase.size = t.erase.size + 1 :=
  RankBalanced.insert_size t g

/-- Insertion keeps the WAVL rule… -/
theorem insert_wavl (t : RankedTree) (g : Nat) (h : Valid .wavl t) : Valid .wavl (insert t g).1 :=
  RankBalanced.insert_wavl t g h

/-- …and the AVL rule (the same procedure is AVL insertion). -/
theorem insert_avl (t : RankedTree) (g : Nat) (h : Valid .avl t) : Valid .avl (insert t g).1 :=
  RankBalanced.insert_avl t g h

/-- **At most two rotations** per insertion. -/
theorem insert_rotations (t : RankedTree) (g : Nat) (h : Valid .wavl t) : (insert t g).2.1 ≤ 2 :=
  RankBalanced.insert_rotations t g h

/-- After `m` insertions into the empty tree the height is at most `log_φ(m + 1)`. -/
theorem insertAll_height (gs : List Nat) :
    (Tree.height (insertAll .nil gs).erase : ℝ) ≤ Real.logb Real.goldenRatio (gs.length + 1) :=
  RankBalanced.insertAll_height gs

/-- **Amortized rank changes**: `m` insertions into the empty tree change at most `7m` ranks. -/
theorem insertEdits_empty (gs : List Nat) : insertEdits .nil gs ≤ 7 * gs.length :=
  RankBalanced.insertEdits_empty gs

end RotationBST.Classical.RankBalanced.Results

/-- info: abstract audit passed for `RotationBST.Classical.RankBalanced.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Classical.RankBalanced.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Dictionary.Definitions.Abstract,
  RotationBST.Classical.RankBalanced.Definitions.Abstract,
  RotationBST.Classical.RankBalanced.Insertion.Definitions.Abstract]
