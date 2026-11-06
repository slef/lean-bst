module

public import RotationBST.Structures.HeavyPath.Finger.Located
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree

private theorem ratio_compare {small large charge target : ℝ}
    (smallPositive : 0 < small) (targetPositive : 0 < target)
    (denominator : target ≤ charge) (numerator : small ≤ large) :
    Real.logb 2 (small / charge) ≤ Real.logb 2 (large / target) := by
  have chargePositive := lt_of_lt_of_le targetPositive denominator
  apply Real.logb_le_logb_of_le (by norm_num) (div_pos smallPositive chargePositive)
  exact (div_le_div_of_nonneg_right numerator chargePositive.le).trans
    (div_le_div_of_nonneg_left (le_of_lt (lt_of_lt_of_le smallPositive numerator)) targetPositive denominator)

/-- The inverted path is crossed once before entering a recursively rebuilt
payload. No light-edge halving assumption is needed for this extra crossing. -/
theorem payload_estimate {whole pair charge child key d : ℝ}
    (keyPositive : 0 < key) (keyMass : key ≤ child) (childCharge : child ≤ charge)
    (chargeMass : charge ≤ pair) (sourceMass : pair ≤ whole)
    (bound : d ≤ 8 + 7 * Real.logb 2 (pair / charge) + (7 + 15 * Real.logb 2 (child / key))) :
    d ≤ 15 + 15 * Real.logb 2 (whole / key) := by
  have childPositive := lt_of_lt_of_le keyPositive keyMass
  have pairPositive := lt_of_lt_of_le childPositive (childCharge.trans chargeMass)
  have wholePositive := lt_of_lt_of_le pairPositive sourceMass
  have logarithm := ratio_compare pairPositive childPositive childCharge sourceMass
  have nonnegative : 0 ≤ Real.logb 2 (whole / child) := by
    apply Real.logb_nonneg (by norm_num)
    exact (le_div_iff₀ childPositive).mpr (by simpa only [one_mul] using childCharge.trans (chargeMass.trans sourceMass))
  have telescoped := Real.logb_mul (div_ne_zero wholePositive.ne' childPositive.ne')
    (div_ne_zero childPositive.ne' keyPositive.ne') (b := (2 : ℝ))
  rw [div_mul_div_cancel₀ childPositive.ne'] at telescoped
  linarith

theorem separator_estimate {whole pair charge key d : ℝ}
    (keyPositive : 0 < key) (keyCharge : key ≤ charge) (chargeMass : charge ≤ pair) (sourceMass : pair ≤ whole)
    (bound : d ≤ 7 + 7 * Real.logb 2 (pair / charge)) :
    d ≤ 15 + 15 * Real.logb 2 (whole / key) := by
  have pairPositive := lt_of_lt_of_le keyPositive (keyCharge.trans chargeMass)
  have logarithm := ratio_compare pairPositive keyPositive keyCharge sourceMass
  have nonnegative : 0 ≤ Real.logb 2 (whole / key) := by
    apply Real.logb_nonneg (by norm_num)
    exact (le_div_iff₀ keyPositive).mpr (by simpa only [one_mul] using keyCharge.trans (chargeMass.trans sourceMass))
  linarith

theorem payload_ranks {α : Type} {weight : α → ℝ} {p : Pair} (valid : p.Valid)
    {whole : ℝ} (sourceMass : p.mass ≤ whole) {subtree : LabelledTree α}
    (positive : Positive weight subtree) {charge : ℝ} (charged : HeavyPath.mass weight subtree ≤ charge)
    {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode.mirror p.upper.decode) (rebuild weight subtree) charge offset depth) :
    RanksSatisfy (fun rank key => (Tree.depth p.tree rank : ℝ) ≤
      15 + 15 * Real.logb 2 (whole / weight key)) offset subtree.inorder := by
  intro before key after split
  obtain ⟨keyPositive, keyMass⟩ := inorder_weight positive (x := key) (by rw [split]; simp)
  have chargePositive := lt_of_lt_of_le keyPositive (keyMass.trans charged)
  have inside : before.length < (rebuild weight subtree).size := by
    rw [rebuild_size positive, ← Representation.Bridge.inorder_length, split]
    simp only [List.length_append, List.length_cons]
    omega
  have bound := located_key_bound valid slot chargePositive before.length inside
  have child := Recursive.rebuild_depth positive split
  apply payload_estimate keyPositive keyMass charged (located_mass valid slot).2 sourceMass
  linarith

end RotationBST.HeavyPath.Finger
