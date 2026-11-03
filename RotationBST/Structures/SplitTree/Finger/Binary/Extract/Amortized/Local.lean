module

public import RotationBST.Structures.SplitTree.Finger.Binary.Extract.Amortized.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Extract.Bounds
import Mathlib.Tactic.SplitIfs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger

theorem repairCredit_root (h : Nat) (t : Multiway) :
    repairCredit h false t ≤ repairCredit h true t ∧
      repairCredit h true t ≤ repairCredit h false t + 3 * h := by
  cases t <;> simp only [repairCredit, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem repairCredit_true (h : Nat) (t : Multiway) :
    repairCredit h true t = repairCredit h false t +
      (if (match t with | .two _ _ => true | _ => false) then 3 * h else 0) := by
  cases t <;> simp [repairCredit]; omega

/-- Height-weighted reserves are still linear in the number of multiway nodes. -/
theorem repairCredit_bound {h : Nat} {t : Multiway} (valid : Balanced h t) (root : Bool) :
    repairCredit h root t + 3 * h ≤ 12 * t.nodes := by
  induction valid generalizing root with
  | nil => simp [repairCredit, nodes]
  | @two k a b ha hb ia ib =>
    have ca := ia true
    have cb := ib false
    cases root <;> simp only [repairCredit, nodes, Nat.add_sub_cancel, Bool.false_eq_true, ite_false, ite_true] <;> omega
  | @three k a b c ha hb hc ia ib ic =>
    have ca := ia true
    have cb := ib false
    have cc := ic false
    simp only [repairCredit, nodes, Nat.add_sub_cancel]
    omega
  | @four k a b c d ha hb hc hd ia ib ic id =>
    have ca := ia true
    have cb := ib false
    have cc := ic false
    have cd := id false
    simp only [repairCredit, nodes, Nat.add_sub_cancel]
    omega

/-- Away from root contraction, a repair pays for itself out of finger credits. -/
theorem repair_credit (k : Nat) (t : Multiway) (root : Bool) (noMerge : t.rootMerge = none) :
    repairOpenCost t + repairCredit (k + 2) root (t.repairFirst).1 ≤ repairCredit (k + 2) root t ∧
      repairViewCost t + repairCredit (k + 2) root (t.repairFirst).1 ≤ repairCredit (k + 2) root t := by
  cases t with
  | nil => simp [repairOpenCost, repairViewCost, repairFirst, prepareLeft, repairCredit]
  | two a b | three a b c | four a b c d =>
    cases a <;> cases b <;>
      simp only [rootMerge, Option.some_ne_none] at noMerge <;>
      simp only [repairOpenCost, repairViewCost, repairFirst, prepareLeft, repairCredit,
        show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel, Bool.false_eq_true, ite_true, ite_false] <;>
      (try simp only [repairCredit_true]) <;>
      (try split_ifs) <;> simp_all +arith

/-- A balanced shallow tree needs no repair; deeper repairs release credit. -/
theorem balanced_repair_credit {h : Nat} {t : Multiway} (valid : Balanced h t)
    (root : Bool) (noMerge : t.rootMerge = none) :
    repairOpenCost t + repairCredit h root (t.repairFirst).1 ≤ repairCredit h root t ∧
      repairViewCost t + repairCredit h root (t.repairFirst).1 ≤ repairCredit h root t := by
  cases h with
  | zero => cases valid; simp [repairOpenCost, repairViewCost, repairFirst, prepareLeft, repairCredit]
  | succ k =>
    cases k with
    | zero =>
      cases valid with
      | two ha hb => cases ha; cases hb; simp [repairOpenCost, repairViewCost, repairFirst, prepareLeft]
      | three ha hb hc => cases ha; cases hb; cases hc; simp [repairOpenCost, repairViewCost, repairFirst, prepareLeft]
      | four ha hb hc hd => cases ha; cases hb; cases hc; cases hd; simp [repairOpenCost, repairViewCost, repairFirst, prepareLeft]
    | succ k => exact repair_credit k t root noMerge

/-- Contracting a minimal root pays its enclosing rotation and adjusts the
height parameter to the contracted tree's height. -/
theorem rootMerge_credit (k : Nat) {t u : Multiway} (merged : t.rootMerge = some u) (root : Bool) :
    1 + repairCredit (k + 1) root u ≤ repairCredit (k + 2) root t := by
  cases t with
  | nil => simp [rootMerge] at merged
  | three a b c => simp [rootMerge] at merged
  | four a b c d => simp [rootMerge] at merged
  | two a b =>
    cases a <;> cases b <;> simp [rootMerge] at merged
    subst u
    simp only [repairCredit, show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel,
      Bool.false_eq_true, ite_false, ite_true]
    simp only [repairCredit_true]
    split_ifs <;> simp_all +arith

end RotationBST.Geometric.Split.Multiway.Finger
