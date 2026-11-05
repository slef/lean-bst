module

public import RotationBST.Algorithms.GreedyASS.Potential.Amortized.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.Bound
public import RotationBST.Algorithms.GreedyASS.Potential.PhaseTwo.Bound
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Amortized
open Items Reference

theorem empty_items (t : Tree) (lo : Nat) (xs : List Nat) (domain : Finset Nat) :
    totalAmount t lo xs ∅ domain = 0 := by
  have unseen : ∀ x, latest ∅ x = none := fun x => (latest_none ∅ x).mpr (by simp)
  simp [totalAmount, itemAmount, itemValue, unseen]

theorem potential_nil (t : Tree) (lo : Nat) : potential t lo [] = 0 := by
  simp [potential, Virgin.points, fill, empty_items]

theorem potential_snoc (t : Tree) (lo : Nat) (xs : List Nat) (x : Nat) :
    potential t lo (xs ++ [x]) =
      totalAmount t lo (xs ++ [x]) (Virgin.points (xs ++ [x])) (Finset.range (lo + leaves t)) +
        Virgin.after t lo xs x := by
  simp [potential, Virgin.before, Virgin.roots_after, Virgin.after]

/-- Both phases combined at successive completed rows. First visits are
kept explicit so their charges can telescope into distinct columns. -/
theorem step (t : Tree) (lo : Nat) (prior : List Nat) (old next : Nat)
    (valid : ∀ x ∈ (prior ++ [old]) ++ [next], lo ≤ x ∧ x < lo + leaves t) :
    (Virgin.keys (prior ++ [old]) next).card + potential t lo ((prior ++ [old]) ++ [next]) ≤
      potential t lo (prior ++ [old]) + 24 * Transitions.edges t lo old next + 24 +
        3 * (unseenKeys (Virgin.points (prior ++ [old])) (Virgin.keys (prior ++ [old]) next)).card := by
  have first := PhaseOne.step t lo prior old next valid (Finset.range (lo + leaves t))
  have second := PhaseTwo.step t lo (prior ++ [old]) next valid
  rw [potential_snoc, potential_snoc]
  omega

theorem edgeCost_snoc (t : Tree) (lo : Nat) (prior : List Nat) (old next : Nat) :
    edgeCost t lo ((prior ++ [old]) ++ [next]) =
      edgeCost t lo (prior ++ [old]) + Transitions.edges t lo old next := by
  induction prior with
  | nil => simp [edgeCost]
  | cons x xs ih =>
    cases xs with
    | nil => simp [edgeCost]
    | cons y ys =>
      simpa only [List.cons_append, edgeCost, Nat.add_assoc] using
        congrArg (fun n => Transitions.edges t lo x y + n) ih

end RotationBST.Geometric.GreedyASS.Potential.Amortized
