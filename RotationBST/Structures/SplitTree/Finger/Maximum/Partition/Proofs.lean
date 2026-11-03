module

public import RotationBST.Structures.SplitTree.Finger.Maximum.Partition.Defs
public import RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Split.Proofs
public import RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Context.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger
open Context

theorem splitLocatedMaximum_shape (t : Multiway) (distance : Nat) :
    let location := locateMaximum t distance
    let cut := Multiway.Partition.run location.height location.focus (location.focus.size - 1 - distance)
    (splitLocatedMaximum t distance).1 =
      .node (maximumEnclosingView cut.left.tree location.outer) (maximumView cut.right.tree).tree := by
  cases rest : maximumContextRemainder (locateMaximum t distance).outer <;>
    simp only [splitLocatedMaximum, rest, maximumEnclosingView, maximumSplit, maximumSplitView]

theorem maximumLocal_rank (t : Multiway) (distance : Nat) (existsKey : distance < t.size) :
    (locateMaximum t distance).focus.size - 1 - distance < (locateMaximum t distance).focus.size := by
  have contains := locateMaximum_contains t distance existsKey
  omega

theorem maximumRepairLocated_balance {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size) :
    Balanced (maximumRepairLocated t distance).height (maximumRepairLocated t distance).tree ∧
      (maximumRepairLocated t distance).height ≤ h := by
  have interval := locateMaximum_balance valid distance
  have contains := maximumLocal_rank t distance existsKey
  have pieces := (Multiway.Partition.run_spec interval.1 _ contains).1
  have heights := Multiway.Partition.run_height interval.1 _ contains
  have result := maximumRepairContext_balance (locateMaximum t distance).outer pieces.1 interval.2
    (fun f member => rightSpine_frames t f (List.mem_of_mem_drop member)) heights.1
  have length := (rightSpine_balanced valid).2
  have enough := ascend_length (rightSpine t) .nil distance
  have total : (locateMaximum t distance).height + (locateMaximum t distance).outer.length = h := by
    simp only [locateMaximum, List.length_drop]
    omega
  exact ⟨result.1, by rw [total] at result; exact result.2⟩

theorem splitFromMaximum_balance {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size) : (splitFromMaximum t distance).Valid :=
  ⟨(maximumRepairLocated_balance valid distance existsKey).1,
    (Multiway.Partition.run_spec (locateMaximum_balance valid distance).1 _
      (maximumLocal_rank t distance existsKey)).1.2⟩

theorem splitFromMaximum_access {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size) :
    Access (maximumView t).tree (maximumSplitView (splitFromMaximum t distance))
      (t.size - 1 - distance) (splitFromMaximum t distance).cost := by
  have localAccess := (splitLocatedMaximum_spec valid distance existsKey).1
  let location := locateMaximum t distance
  let cut := Multiway.Partition.run location.height location.focus (location.focus.size - 1 - distance)
  have repairs := maximumRepairContext_rotations location.outer location.height cut.left.height cut.left.tree
    (fun f member => rightSpine_frames t f (List.mem_of_mem_drop member))
  rw [splitLocatedMaximum_shape] at localAccess
  constructor
  · exact localAccess.1.append repairs.inLeft
  · have sizes := repairs.size_eq
    change (maximumEnclosingView cut.left.tree location.outer).size = _ at sizes
    change (maximumView (maximumRepairLocated t distance).tree).tree.size = _
    exact sizes.symm.trans localAccess.2

theorem splitFromMaximum_sizes {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size) :
    (splitFromMaximum t distance).left.tree.size = t.size - 1 - distance ∧
      (splitFromMaximum t distance).right.tree.size = distance := by
  have access := splitFromMaximum_access valid distance existsKey
  have left := access.2
  change (maximumView (splitFromMaximum t distance).left.tree).tree.size = _ at left
  rw [maximumView_size] at left
  have sizes := access.1.size_eq
  simp only [maximumSplitView, Tree.size, maximumView_size] at sizes
  exact ⟨left, by omega⟩

end RotationBST.Geometric.Split.Multiway.Finger
