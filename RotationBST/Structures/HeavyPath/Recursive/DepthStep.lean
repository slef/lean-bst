module

public import RotationBST.Structures.HeavyPath.Recursive.LightMass
public import RotationBST.Structures.HeavyPath.Paired.Located
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive
open Paired PopTart PopTart.WeightedTree LabelledCursor

theorem rootPair_source {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    (rootPair weight t).Valid ∧ (rootPair weight t).mass ≤ HeavyPath.mass weight t ∧
      rebuild weight t = (rootPair weight t).tree := by
  obtain ⟨endpoint, focus, tree, valid, partition, fringe⟩ := rebuild_pair positive nonempty
  have endpointPositive := (HeavyPath.Results.extract_positive positive).1
  rw [focus] at endpointPositive
  have own : 0 < weight endpoint := endpointPositive.2.1
  exact ⟨valid, by dsimp only [rootPair]; linarith only [partition, own], tree⟩

private theorem ratio_compare {small large charge target : ℝ}
    (smallPositive : 0 < small) (targetPositive : 0 < target)
    (denominator : target ≤ charge) (numerator : small ≤ large) :
    Real.logb 2 (small / charge) ≤ Real.logb 2 (large / target) := by
  have chargePositive := lt_of_lt_of_le targetPositive denominator
  apply Real.logb_le_logb_of_le (by norm_num) (div_pos smallPositive chargePositive)
  exact (div_le_div_of_nonneg_right numerator chargePositive.le).trans
    (div_le_div_of_nonneg_left (le_of_lt (lt_of_lt_of_le smallPositive numerator)) targetPositive denominator)

/-- Each light-edge crossing can absorb its additive eight units into the
logarithm. The logarithmic terms then telescope, with coefficient fifteen. -/
theorem depth_telescope {whole child key d : ℝ}
    (keyPositive : 0 < key) (keyMass : key ≤ child) (half : 2 * child ≤ whole)
    (bound : d ≤ 8 + 7 * Real.logb 2 (whole / child) + (7 + 15 * Real.logb 2 (child / key))) :
    d ≤ 7 + 15 * Real.logb 2 (whole / key) := by
  have childPositive : 0 < child := lt_of_lt_of_le keyPositive keyMass
  have wholePositive : 0 < whole := by linarith
  have ratio : (2 : ℝ) ≤ whole / child := (le_div_iff₀ childPositive).mpr half
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) ratio
  simp only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at logarithm
  have telescoped := Real.logb_mul (div_ne_zero wholePositive.ne' childPositive.ne')
    (div_ne_zero childPositive.ne' keyPositive.ne') (b := (2 : ℝ))
  rw [div_mul_div_cancel₀ childPositive.ne'] at telescoped
  linarith

/-- The recursive induction step for a key inside a specified off-path
occurrence. The caller supplies the child's bound; no global bound is assumed. -/
theorem payload_depth_step {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil)
    {frame : Frame α} (member : frame ∈ (extract weight t).context) {offset depth x : Nat} {keyWeight : ℝ}
    (slot : LocatedSlot (.node (rootPair weight t).lower.decode (rootPair weight t).upper.decode.mirror)
      (rebuild weight (framePayload frame)) (frameMass weight frame) offset depth)
    (inside : x < (rebuild weight (framePayload frame)).size)
    (keyPositive : 0 < keyWeight) (keyMass : keyWeight ≤ HeavyPath.mass weight (framePayload frame))
    (childBound : (Tree.depth (rebuild weight (framePayload frame)) x : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight (framePayload frame) / keyWeight)) :
    (Tree.depth (rebuild weight t) (offset + x) : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / keyWeight) := by
  obtain ⟨valid, sourceMass, tree⟩ := rootPair_source positive nonempty
  have charges := extract_charge_bounds positive member
  have chargePositive := lt_of_lt_of_le charges.1 charges.2.1
  have slotMass := (located_mass valid slot).2
  have pairPositive := lt_of_lt_of_le chargePositive slotMass
  have childPositive := lt_of_lt_of_le keyPositive keyMass
  have logarithm := ratio_compare pairPositive childPositive charges.2.2 sourceMass
  have entry := located_key_bound valid slot chargePositive x inside
  rw [← tree] at entry
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
    (positive : Positive weight t) (nonempty : t ≠ .nil)
    {frame : Frame α} (member : frame ∈ (extract weight t).context) {offset depth : Nat}
    (slot : LocatedSlot (.node (rootPair weight t).lower.decode (rootPair weight t).upper.decode.mirror)
      (rebuild weight (framePayload frame)) (frameMass weight frame) offset depth)
    (existsKey : offset + (rebuild weight (framePayload frame)).size < (rebuild weight t).size) :
    (Tree.depth (rebuild weight t) (offset + (rebuild weight (framePayload frame)).size) : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight (frameKey frame)) := by
  obtain ⟨valid, sourceMass, tree⟩ := rootPair_source positive nonempty
  have charges := extract_charge_bounds positive member
  have chargePositive := lt_of_lt_of_le charges.1 charges.2.1
  have bound := located_successor_bound valid slot chargePositive (by simpa only [tree] using existsKey)
  rw [← tree] at bound
  exact separator_estimate charges.1 charges.2.1 (located_mass valid slot).2 sourceMass bound

theorem predecessor_depth_step {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil)
    {frame : Frame α} (member : frame ∈ (extract weight t).context) {offset depth : Nat}
    (slot : LocatedSlot (.node (rootPair weight t).lower.decode (rootPair weight t).upper.decode.mirror)
      (rebuild weight (framePayload frame)) (frameMass weight frame) offset depth)
    (existsKey : 0 < offset) :
    (Tree.depth (rebuild weight t) (offset - 1) : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight (frameKey frame)) := by
  obtain ⟨valid, sourceMass, tree⟩ := rootPair_source positive nonempty
  have charges := extract_charge_bounds positive member
  have chargePositive := lt_of_lt_of_le charges.1 charges.2.1
  have bound := located_predecessor_bound valid slot chargePositive existsKey
  rw [← tree] at bound
  exact separator_estimate charges.1 charges.2.1 (located_mass valid slot).2 sourceMass bound

end RotationBST.HeavyPath.Recursive
