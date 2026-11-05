module

public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.History
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Unaccessed
open Items Reference

/-- Every internal point in an actual greedy history has its red candidate
covered by the historical purple maximum. This supplies Lemma 3.16 when an
unaccessed glancing point becomes internal on the next row. -/
theorem internal_purple (t : Tree) (lo : Nat) (searches : List Nat) {n : Nat}
    (valid : ∀ y ∈ searches, y < n) {q : Point} (internal : Internal (Virgin.points searches) q) :
    red t lo (Virgin.points searches) q ≤ WithTop.some (purple t lo searches q.2 q.1) := by
  obtain ⟨a, b, left, right, ax, xb, value⟩ := red_finite t lo internal.1 internal.2.1
  obtain ⟨u, hu, v, hv, ua, bv⟩ := internal_bracket searches valid internal left right
  have enclosure := Distance.enclosing t lo q.1 u a b v ua (by omega) bv
  have blueBound := enclosing_blue t lo u q.1 v (by omega) (by omega)
  have blueU : blue t lo u q.1 ≤ purple t lo searches q.2 q.1 :=
    Finset.le_sup (f := fun s => blue t lo s q.1) (List.mem_toFinset.mpr hu)
  have blueV : blue t lo v q.1 ≤ purple t lo searches q.2 q.1 :=
    Finset.le_sup (f := fun s => blue t lo s q.1) (List.mem_toFinset.mpr hv)
  rw [value]
  exact WithTop.coe_le_coe.mpr (enclosure.trans (blueBound.trans (max_le blueU blueV)))

/-- Lemma 3.17 for actual greedy histories. The glancing-to-internal branch
uses the historical bound above; stable geometry uses unchanged candidates. -/
theorem nonexternal_value (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat) {n : Nat}
    (valid : ∀ y ∈ searches ++ [searched], y < n) {q : Point}
    (active : Active (Virgin.points searches) q) (nonexternal : ¬ External (Virgin.points searches) q)
    (untouched : q.1 ∉ Virgin.keys searches searched) :
    value t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched])) q ≤
      value t lo (searches ++ [searched]) (Virgin.points searches) q := by
  have history := Virgin.points_history n searches (fun y hy => valid y (List.mem_append_left _ hy))
  have newActive : Active (Virgin.points (searches ++ [searched])) q := by
    rw [Virgin.points_snoc]
    exact (active_unchanged _ _ _ q untouched).mpr active
  have newNonexternal : ¬ External (Virgin.points (searches ++ [searched])) q := by
    rw [Virgin.points_snoc]
    exact fun ext => nonexternal ((external_unchanged _ history active untouched).mp ext)
  by_cases glancing : Glancing (Virgin.points searches) q
  · by_cases newGlancing : Glancing (Virgin.points (searches ++ [searched])) q
    · rw [Virgin.points_snoc] at newGlancing ⊢
      exact le_of_eq (glancing_unchanged t lo (searches ++ [searched]) _ history glancing newGlancing).2
    · have internal : Internal (Virgin.points (searches ++ [searched])) q :=
        ⟨newActive, newNonexternal, newGlancing⟩
      have purpleBound := internal_purple t lo (searches ++ [searched]) valid internal
      rw [(internal_spec t lo (searches ++ [searched]) internal).2,
        (glancing_spec t lo (searches ++ [searched]) glancing).2]
      apply le_min
      · rw [Virgin.points_snoc, red_unchanged t lo _ history active.1]
      · exact purpleBound
  · have internal : Internal (Virgin.points searches) q := ⟨active, nonexternal, glancing⟩
    rw [Virgin.points_snoc]
    exact le_of_eq (Potential.internal_unchanged t lo (searches ++ [searched]) _ history internal untouched)

end RotationBST.Geometric.GreedyASS.Potential.Unaccessed
