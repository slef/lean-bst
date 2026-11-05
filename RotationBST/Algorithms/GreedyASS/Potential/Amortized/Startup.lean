module

public import RotationBST.Algorithms.GreedyASS.Potential.Amortized.Step
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Amortized
open Reference

theorem forest_length (t : Tree) (lo searched : Nat) :
    (forest t lo searched).length ≤ leaves t := by
  induction t generalizing lo with
  | nil => simp [forest, leaves]
  | node l r ihl ihr =>
    have := leaves_positive l
    have := leaves_positive r
    simp only [forest, leaves]
    split
    · simpa only [List.length_append, List.length_singleton] using
        (show (forest l lo searched).length + 1 ≤ leaves l + leaves r by
          have := ihl lo
          omega)
    · simp only [List.length_cons]
      have := ihr (lo + leaves l)
      omega

theorem virgin_bound (t : Tree) (lo : Nat) (xs : List Nat) (searched : Nat) :
    Virgin.before t lo xs searched ≤ 12 * leaves t := by
  classical
  have filtered := Finset.card_filter_le (forest t lo searched).toFinset
    (fun c => ¬ Virgin.NonVirgin t lo xs searched c)
  have dedup := List.toFinset_card_le (forest t lo searched)
  have length := forest_length t lo searched
  unfold Virgin.before Virgin.roots
  omega

/-- Initial virgin roots require at most twelve credits per reference leaf;
the initial item potential is zero. -/
theorem startup (t : Tree) (lo searched : Nat)
    (valid : lo ≤ searched ∧ searched < lo + leaves t) :
    (Virgin.keys [] searched).card + potential t lo [searched] ≤
      12 * leaves t + 24 + 3 * (unseenKeys (Virgin.points []) (Virgin.keys [] searched)).card := by
  have bound := PhaseTwo.step t lo [] searched (by simpa using valid)
  have virgin := virgin_bound t lo [] searched
  have empty : Virgin.points [] = ∅ := rfl
  rw [empty, empty_items] at bound
  rw [show [searched] = [] ++ [searched] from rfl, potential_snoc]
  rw [empty]
  omega

end RotationBST.Geometric.GreedyASS.Potential.Amortized
