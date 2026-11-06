module

public import RotationBST.Structures.HeavyPath.Recursive.History.Preservation
public import RotationBST.Structures.HeavyPath.Paired.Located
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History
open Paired PopTart PopTart.WeightedTree LabelledCursor

private theorem ratio_compare {small large charge target : ℝ}
    (smallPositive : 0 < small) (targetPositive : 0 < target)
    (denominator : target ≤ charge) (numerator : small ≤ large) :
    Real.logb 2 (small / charge) ≤ Real.logb 2 (large / target) := by
  have chargePositive := lt_of_lt_of_le targetPositive denominator
  apply Real.logb_le_logb_of_le (by norm_num) (div_pos smallPositive chargePositive)
  exact (div_le_div_of_nonneg_right numerator chargePositive.le).trans
    (div_le_div_of_nonneg_left (le_of_lt (lt_of_lt_of_le smallPositive numerator)) targetPositive denominator)

/-- The recursive induction step for a key inside a specified off-path
occurrence. The caller supplies the child's bound; no global bound is assumed. -/
theorem payload_depth_step {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {p : Stacks} (valid : p.Valid) (sourceMass : p.mass ≤ mass weight t)
    {shape : Tree} {frame : Frame α} (member : frame ∈ (extract weight t).context) {offset depth x : Nat} {keyWeight : ℝ}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror)
      shape (frameMass weight frame) offset depth)
    (inside : x < shape.size)
    (keyPositive : 0 < keyWeight) (keyMass : keyWeight ≤ HeavyPath.mass weight (framePayload frame))
    (childBound : (Tree.depth shape x : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight (framePayload frame) / keyWeight)) :
    (Tree.depth p.tree (offset + x) : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / keyWeight) := by
  have charges := extract_charge_bounds positive member
  have chargePositive := lt_of_lt_of_le charges.1 charges.2.1
  have slotMass := (located_mass valid slot).2
  have pairPositive := lt_of_lt_of_le chargePositive slotMass
  have childPositive := lt_of_lt_of_le keyPositive keyMass
  have logarithm := ratio_compare pairPositive childPositive charges.2.2 sourceMass
  have entry := located_key_bound valid slot chargePositive x inside
  apply depth_telescope keyPositive keyMass (extract_payload_half positive member)
  linarith

private theorem separator_estimate {P W charge key d : ℝ}
    (keyPositive : 0 < key) (keyCharge : key ≤ charge) (chargeMass : charge ≤ P) (sourceMass : P ≤ W)
    (bound : d ≤ 7 + 7 * Real.logb 2 (P / charge)) : d ≤ 7 + 15 * Real.logb 2 (W / key) := by
  have pairPositive := lt_of_lt_of_le (lt_of_lt_of_le keyPositive keyCharge) chargeMass
  have logarithm := ratio_compare pairPositive keyPositive keyCharge sourceMass
  have nonnegative : 0 ≤ Real.logb 2 (W / key) := by
    apply Real.logb_nonneg (by norm_num)
    exact (le_div_iff₀ keyPositive).mpr (by simpa only [one_mul] using keyCharge.trans (chargeMass.trans sourceMass))
  linarith

theorem successor_depth_step {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {p : Stacks} (valid : p.Valid) (sourceMass : p.mass ≤ mass weight t)
    {shape : Tree} {frame : Frame α} (member : frame ∈ (extract weight t).context) {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror)
      shape (frameMass weight frame) offset depth)
    (existsKey : offset + shape.size < p.tree.size) :
    (Tree.depth p.tree (offset + shape.size) : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight (frameKey frame)) := by
  have charges := extract_charge_bounds positive member
  have chargePositive := lt_of_lt_of_le charges.1 charges.2.1
  have bound := located_successor_bound valid slot chargePositive existsKey
  exact separator_estimate charges.1 charges.2.1 (located_mass valid slot).2 sourceMass bound

theorem predecessor_depth_step {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {p : Stacks} (valid : p.Valid) (sourceMass : p.mass ≤ mass weight t)
    {shape : Tree} {frame : Frame α} (member : frame ∈ (extract weight t).context) {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror)
      shape (frameMass weight frame) offset depth)
    (existsKey : 0 < offset) :
    (Tree.depth p.tree (offset - 1) : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight (frameKey frame)) := by
  have charges := extract_charge_bounds positive member
  have chargePositive := lt_of_lt_of_le charges.1 charges.2.1
  have bound := located_predecessor_bound valid slot chargePositive existsKey
  exact separator_estimate charges.1 charges.2.1 (located_mass valid slot).2 sourceMass bound

end RotationBST.HeavyPath.Recursive.History
