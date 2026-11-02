module

public import RotationBST.Splay.Potential
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Nodup

@[expose] public section

namespace RotationBST.Recency

variable {order : List Nat} {x y : Nat}

/-- Move a key to the front of the recency order. -/
def touch (order : List Nat) (x : Nat) : List Nat := x :: order.erase x

/-- Recency order after a chronological request history. -/
def after (order : List Nat) : List Nat → List Nat
  | [] => order
  | x :: xs => after (touch order x) xs

/-- The analysis weight of a key at one-based recency position `r` is `1/r²`.
Absent keys receive the positive weight at position `length + 1`. -/
noncomputable def weight (order : List Nat) (x : Nat) : ℝ :=
  (((order.idxOf x : ℝ) + 1) ^ 2)⁻¹

theorem weight_pos (order : List Nat) (x : Nat) : 0 < weight order x := by
  unfold weight
  positivity

theorem touch_perm (order : List Nat) (hx : x ∈ order) : (touch order x).Perm order :=
  (List.perm_cons_erase hx).symm

theorem touch_nodup (h : order.Nodup) (hx : x ∈ order) : (touch order x).Nodup :=
  (touch_perm order hx).nodup_iff.mpr h

theorem touch_length (hx : x ∈ order) : (touch order x).length = order.length :=
  (touch_perm order hx).length_eq

theorem idxOf_erase_le (order : List Nat) (x y : Nat) :
    order.idxOf y ≤ (order.erase x).idxOf y + 1 := by
  induction order with
  | nil => simp
  | cons a order ih =>
      by_cases hx : a = x
      · subst a
        by_cases hy : x = y
        · subst y; simp
        · simp [List.erase_cons_head, hy]
      · by_cases hy : a = y
        · subst a; simp
        · simpa [List.erase_cons, List.idxOf_cons, hx, hy] using ih

theorem rank_touch_le (order : List Nat) (hne : x ≠ y) :
    order.idxOf y ≤ (touch order x).idxOf y := by
  simpa [touch, List.idxOf_cons, hne] using idxOf_erase_le order x y

/-- Only the accessed key's weight can increase. -/
theorem weight_touch_le (order : List Nat) (hne : x ≠ y) :
    weight (touch order x) y ≤ weight order y := by
  have h := rank_touch_le order hne
  have hr : (order.idxOf y : ℝ) ≤ (touch order x).idxOf y := by exact_mod_cast h
  unfold weight
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg ((touch order x).idxOf y - (order.idxOf y : ℝ))]

theorem weight_touch_self (order : List Nat) (x : Nat) : weight (touch order x) x = 1 := by
  simp [weight, touch]

/-- Enumerating a duplicate-free list by its own indices gives `0,…,n-1`. -/
theorem map_idxOf (order : List Nat) (h : order.Nodup) :
    order.map order.idxOf = List.range order.length := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map] at hi
    simp [h.idxOf_getElem i hi]

theorem weight_lower (order : List Nat) (x : Nat) :
    (((order.length : ℝ) + 1) ^ 2)⁻¹ ≤ weight order x := by
  have hr : (order.idxOf x : ℝ) ≤ order.length := by exact_mod_cast List.idxOf_le_length
  unfold weight
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg ((order.length : ℝ) - order.idxOf x)]

end RotationBST.Recency
