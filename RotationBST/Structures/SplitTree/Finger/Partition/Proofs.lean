module

public import RotationBST.Structures.SplitTree.Finger.Partition.Defs
public import RotationBST.Structures.SplitTree.Finger.Locate.Split.Proofs
public import RotationBST.Structures.SplitTree.Finger.Repair.Context.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

theorem splitLocated_shape (t : Multiway) (rank : Nat) :
    let location := locate t rank
    let cut := Multiway.Partition.run location.height location.focus rank
    (splitLocated t rank).1 = .node (binaryView cut.left.tree).tree (enclosingView cut.right.tree location.outer) := by
  cases rest : contextRemainder (locate t rank).outer <;>
    simp only [splitLocated, rest, enclosingView, fingerSplit, splitView]

theorem repairLocated_balance {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    Balanced (repairLocated t rank).height (repairLocated t rank).tree ∧
      (repairLocated t rank).height ≤ h := by
  have interval := locate_balance valid rank
  have contains := locate_contains t rank existsKey
  have pieces := (Multiway.Partition.run_spec interval.1 rank contains).1
  have heights := Multiway.Partition.run_height interval.1 rank contains
  have result := repairContext_balance (locate t rank).outer pieces.2 interval.2
    (fun f member => leftSpine_frames t f (List.mem_of_mem_drop member)) heights.2
  have length := (leftSpine_balanced valid).2
  have enough := ascend_length (leftSpine t) .nil rank
  change searchLevels t rank ≤ (leftSpine t).length at enough
  have total : (locate t rank).height + (locate t rank).outer.length = h := by
    simp only [locate, List.length_drop]
    omega
  exact ⟨result.1, by rw [total] at result; exact result.2⟩

theorem splitFromMinimum_balance {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) : (splitFromMinimum t rank).Valid := by
  have interval := (locate_balance valid rank).1
  have contains := locate_contains t rank existsKey
  exact ⟨(Multiway.Partition.run_spec interval rank contains).1.1,
    (repairLocated_balance valid rank existsKey).1⟩

theorem splitFromMinimum_access {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    Access (binaryView t).tree (splitView (splitFromMinimum t rank)) rank (splitFromMinimum t rank).cost := by
  have localAccess := (splitLocated_spec valid rank existsKey).1
  have repairs := repairContext_rotations (locate t rank).outer (locate t rank).height
    (Multiway.Partition.run (locate t rank).height (locate t rank).focus rank).right.height
    (Multiway.Partition.run (locate t rank).height (locate t rank).focus rank).right.tree
    (fun f member => leftSpine_frames t f (List.mem_of_mem_drop member))
  constructor
  · rw [splitLocated_shape] at localAccess
    exact localAccess.1.append repairs.inRight
  · change (binaryView (Multiway.Partition.run (locate t rank).height (locate t rank).focus rank).left.tree).tree.size = rank
    rw [binaryView_size]
    exact (Multiway.Partition.run_sizes (locate_balance valid rank).1 rank (locate_contains t rank existsKey)).1

theorem splitFromMinimum_sizes {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    (splitFromMinimum t rank).left.tree.size = rank ∧
      (splitFromMinimum t rank).right.tree.size = t.size - rank - 1 := by
  have access := splitFromMinimum_access valid rank existsKey
  have left := access.2
  change (binaryView (splitFromMinimum t rank).left.tree).tree.size = rank at left
  rw [binaryView_size] at left
  have sizes := access.1.size_eq
  simp only [splitView, Tree.size, binaryView_size] at sizes
  exact ⟨left, by omega⟩

end RotationBST.Arboral.Split.Multiway.Finger
