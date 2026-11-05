module

public import RotationBST.Structures.PrefixSum.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PrefixSum

theorem row_size (f : Nat → Nat) (n : Nat) : (row f n).size = n + 1 := by
  induction n with
  | zero => simp [row]
  | succ n ih => simp [row, ih]

theorem row_get (f : Nat → Nat) (n b : Nat) (hb : b ≤ n) :
    (row f n)[b]?.getD 0 = ∑ j ∈ Finset.range b, f j := by
  induction n generalizing b with
  | zero =>
    have he : b = 0 := by omega
    subst b
    simp [row]
  | succ n ih =>
    by_cases old : b ≤ n
    · have hne : b ≠ (row f n).size := by rw [row_size]; omega
      simpa only [row, Array.getElem?_push, hne, ↓reduceIte] using ih b old
    · have he : b = n + 1 := by omega
      subst b
      simp only [row, Array.getElem?_push, row_size, ↓reduceIte, Option.getD_some,
        ih n le_rfl, Finset.sum_range_succ]

theorem build_size (f : Nat → Nat → Nat) (width height : Nat) :
    (build f width height).size = height + 1 := by
  induction height with
  | zero => simp [build]
  | succ height ih => simp only [build, Array.size_push, ih]

theorem build_get (f : Nat → Nat → Nat) (width height a b : Nat)
    (ha : a ≤ height) (hb : b ≤ width) : get (build f width height) a b = sumPrefix f a b := by
  induction height generalizing a with
  | zero =>
    have he : a = 0 := by omega
    subst a
    simp [get, build, sumPrefix, show b < width + 1 by omega]
  | succ height ih =>
    by_cases old : a ≤ height
    · have hne : a ≠ (build f width height).size := by rw [build_size]; omega
      simpa only [build, get, Array.getElem?_push, hne, ↓reduceIte] using ih a old
    · have he : a = height + 1 := by omega
      subst a
      simp only [build, get, Array.getElem?_push, build_size, ↓reduceIte,
        Option.getD_some, Array.getElem?_ofFn, show b < width + 1 by omega, ↓reduceDIte]
      change get (build f width height) height b + (row (f height) width)[b]?.getD 0 = _
      rw [ih height le_rfl, row_get _ _ b hb]
      simp only [sumPrefix, Finset.sum_range_succ]

/-- Inclusion-exclusion identity stated without subtraction. -/
theorem rectangle_balance (f : Nat → Nat → Nat) (a b c d : Nat)
    (hab : a ≤ b) (hcd : c ≤ d) :
    (∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico c d, f i j) + sumPrefix f a d + sumPrefix f b c =
      sumPrefix f b d + sumPrefix f a c := by
  have hi := Finset.sum_range_add_sum_Ico (fun i => ∑ j ∈ Finset.range d, f i j) hab
  have hi' := Finset.sum_range_add_sum_Ico (fun i => ∑ j ∈ Finset.range c, f i j) hab
  have hj : (∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.range c, f i j) +
      (∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico c d, f i j) =
      ∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.range d, f i j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_range_add_sum_Ico (f i) hcd)
  unfold sumPrefix
  omega

/-- Four lookups in the cached table give the exact rectangle sum. -/
theorem rectangle_build (f : Nat → Nat → Nat) (width height a b c d : Nat)
    (hab : a ≤ b) (hb : b ≤ height) (hcd : c ≤ d) (hd : d ≤ width) :
    rectangle (build f width height) a b c d = ∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico c d, f i j := by
  rw [rectangle, build_get _ _ _ b d hb hd, build_get _ _ _ a c (by omega) (by omega),
    build_get _ _ _ a d (by omega) hd, build_get _ _ _ b c hb (by omega)]
  have h := rectangle_balance f a b c d hab hcd
  omega

end RotationBST.PrefixSum
