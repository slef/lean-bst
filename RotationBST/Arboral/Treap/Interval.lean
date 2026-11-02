module

public import RotationBST.Arboral.Treap.Priorities
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Nat.Dist

@[expose] public section
namespace RotationBST.Arboral

/-- A minimum next-touch priority among current-row keys of an interval is
also a minimum among all keys of that interval. This includes never-used keys. -/
theorem interval_minimum {P : Finset Point} {time low high root key : Nat}
    (sat : ASS P) (current : (root, time) ∈ P)
    (rootlow : low ≤ root) (roothigh : root < high)
    (keylow : low ≤ key) (keyhigh : key < high)
    (minimum : ∀ x, (x, time) ∈ P → low ≤ x → x < high →
      nextTouch P (time + 1) root ≤ nextTouch P (time + 1) x) :
    nextTouch P (time + 1) root ≤ nextTouch P (time + 1) key := by
  classical
  let S := P.filter fun p => p.2 = time ∧ min root key ≤ p.1 ∧ p.1 ≤ max root key
  have hroot : (root, time) ∈ S := Finset.mem_filter.mpr
    ⟨current, rfl, min_le_left _ _, le_max_left _ _⟩
  obtain ⟨a, ha, hmin⟩ := S.exists_min_image (fun p => Nat.dist p.1 key) ⟨_, hroot⟩
  obtain ⟨haP, hat, halo, hahi⟩ := Finset.mem_filter.mp ha
  have haCurrent : (a.1, time) ∈ P := by simpa only [← hat, Prod.eta] using haP
  have hroota := minimum a.1 haCurrent (by omega) (by omega)
  by_cases he : a.1 = key
  · simpa only [he] using hroota
  apply hroota.trans
  apply adjacent_nextTouch sat haCurrent he
  intro x hx hxlo hxhi
  have hxS : (x, time) ∈ S := Finset.mem_filter.mpr ⟨hx, rfl, by omega, by omega⟩
  have hd := hmin (x, time) hxS
  simp only [Nat.dist] at hd
  omega

end RotationBST.Arboral
