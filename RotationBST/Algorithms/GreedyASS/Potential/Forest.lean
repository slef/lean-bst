module

public import RotationBST.Algorithms.GreedyASS.Potential.Neighbors
public import RotationBST.Algorithms.GreedyASS.Reference.Distance.Components
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential
open Items Reference

theorem blue_ge_two (t : Tree) (lo searched x : Nat) : 2 ≤ blue t lo searched x := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    unfold blue
    split <;> split
    · exact il lo
    · omega
    · omega
    · exact ir (lo + leaves l)

/-- The executable blue query uses exactly the containing root of the
existing reference forest, including the searched singleton. -/
theorem blue_component (t : Tree) (lo searched x : Nat) {c : Component}
    (member : c ∈ forest t lo searched) (inside : c.Contains x) :
    blue t lo searched x = Distance.toRoot c x + 1 := by
  induction t generalizing lo with
  | nil =>
    have eq : c = ⟨lo, .nil⟩ := by simpa only [forest, List.mem_singleton] using member
    subst c
    rfl
  | node l r il ir =>
    by_cases searchLeft : searched < lo + leaves l
    · simp only [forest, ite_eq_left searchLeft, List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · have bounds := Reference.bounds l lo searched member
        have xLeft : x < lo + leaves l := lt_of_lt_of_le inside.2 bounds.2
        simpa only [blue, ite_eq_left searchLeft, ite_eq_left xLeft] using il lo member
      · have xRight : ¬ x < lo + leaves l := Nat.not_lt.mpr inside.1
        simp [blue, searchLeft, xRight, Distance.toRoot, Nat.add_assoc]
    · simp only [forest, ite_eq_right searchLeft, List.mem_cons] at member
      rcases member with rfl | member
      · have xLeft : x < lo + leaves l := inside.2
        simp [blue, searchLeft, xLeft, Distance.toRoot, Nat.add_assoc]
      · have bounds := Reference.bounds r (lo + leaves l) searched member
        have xRight : ¬ x < lo + leaves l := by
          have := inside.1
          omega
        simpa only [blue, ite_eq_right searchLeft, ite_eq_right xRight] using
          ir (lo + leaves l) member

theorem green_missing (t : Tree) (lo : Nat) (P : Finset Point) (x : Nat)
    (missing : leftExternal P x = none ∨ rightExternal P x = none) : green t lo P x = ⊤ := by
  rcases missing with left | right
  · simp [green, left]
  · cases leftExternal P x <;> simp [green, right]

/-- With both external neighbors present, green is no larger than blue
exactly when both neighbors lie in the item's current reference component. -/
theorem green_blue (t : Tree) (lo searched : Nat) (P : Finset Point) (x a b : Nat)
    {c : Component} (member : c ∈ forest t lo searched) (inside : c.Contains x)
    (left : leftExternal P x = some a) (right : rightExternal P x = some b)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) :
    green t lo P x ≤ (blue t lo searched x : WithTop Nat) ↔ c.Contains a ∧ c.Contains b := by
  have ha := (left_external_spec P x a).mp left
  have hb := (right_external_spec P x b).mp right
  obtain ⟨ta, externalA⟩ := (mem_external P a).mp ha.1
  obtain ⟨tb, externalB⟩ := (mem_external P b).mp hb.1
  have validA := valid (a, ta) (externalA.elim (fun h => h.1.1) (fun h => h.1.1))
  have validB := valid (b, tb) (externalB.elim (fun h => h.1.1) (fun h => h.1.1))
  rw [green, left, right, blue_component t lo searched x member inside]
  simpa only [WithTop.coe_le_coe, Nat.add_le_add_iff_right] using
    Distance.forest_compare t lo searched a x b member inside ha.2.1.le hb.2.1.le validA validB

theorem purple_step (t : Tree) (lo : Nat) (searches : List Nat) (searched stamp x : Nat)
    (old : stamp ≤ searches.length) :
    purple t lo (searches ++ [searched]) stamp x =
      max (purple t lo searches stamp x) (blue t lo searched x) := by
  simp [purple, List.drop_append_of_le_length old, max_comm]

theorem purple_reset (t : Tree) (lo : Nat) (searches : List Nat) (searched x : Nat) :
    purple t lo (searches ++ [searched]) searches.length x = blue t lo searched x := by
  simp [purple]

theorem purple_ge_blue (t : Tree) (lo : Nat) (searches : List Nat) (searched stamp x : Nat)
    (old : stamp ≤ searches.length) :
    blue t lo searched x ≤ purple t lo (searches ++ [searched]) stamp x := by
  rw [purple_step t lo searches searched stamp x old]
  exact le_max_right _ _

end RotationBST.Geometric.GreedyASS.Potential
