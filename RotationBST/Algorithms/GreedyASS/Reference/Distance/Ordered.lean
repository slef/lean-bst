module

public import RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Distance

theorem self (t : Tree) (lo x : Nat) : lcaDepth t lo x x = depth t lo x := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    by_cases side : x < lo + leaves l
    · simp [lcaDepth, depth, side, il]
    · simp [lcaDepth, depth, side, Nat.le_of_not_gt side, ir]

theorem symmetric (t : Tree) (lo a b : Nat) : lcaDepth t lo a b = lcaDepth t lo b a := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir => simp only [lcaDepth, and_comm, il, ir]

/-- Enlarging an ordered leaf interval can only move its LCA upward. Weak
inequalities include coincident endpoints and singleton intervals. -/
theorem interval (t : Tree) (lo a b c d : Nat) (ab : a ≤ b) (bc : b ≤ c) (cd : c ≤ d) :
    lcaDepth t lo a d ≤ lcaDepth t lo b c := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    by_cases left : a < lo + leaves l ∧ d < lo + leaves l
    · have middle : b < lo + leaves l ∧ c < lo + leaves l := by omega
      simpa only [lcaDepth, ite_eq_left left, ite_eq_left middle, Nat.add_le_add_iff_right] using il lo
    · by_cases right : lo + leaves l ≤ a ∧ lo + leaves l ≤ d
      · have middle : lo + leaves l ≤ b ∧ lo + leaves l ≤ c := by omega
        have notLeft : ¬ (b < lo + leaves l ∧ c < lo + leaves l) := by omega
        simpa only [lcaDepth, ite_eq_right left, ite_eq_right notLeft, ite_eq_left right, ite_eq_left middle,
          Nat.add_le_add_iff_right] using ir (lo + leaves l)
      · simp only [lcaDepth, left, right, ↓reduceIte]
        exact Nat.zero_le _

theorem below_leaf (t : Tree) (lo a x b : Nat) (ax : a ≤ x) (xb : x ≤ b) :
    lcaDepth t lo a b ≤ depth t lo x := by
  simpa only [self] using interval t lo a x x b ax le_rfl xb

/-- Distance to the LCA is monotone under enlargement of its endpoint interval. -/
theorem enclosing (t : Tree) (lo x a b c d : Nat) (ab : a ≤ b) (bc : b ≤ c) (cd : c ≤ d) :
    toLCA t lo x b c ≤ toLCA t lo x a d := by
  have := interval t lo a b c d ab bc cd
  unfold toLCA
  omega

/-- Fact 3.1, with weak ordering so later applications can reuse endpoints. -/
theorem four_leaves (t : Tree) (lo w x y z : Nat) (wx : w ≤ x) (xy : x ≤ y) (yz : y ≤ z) :
    toLCA t lo x w y ≤ toLCA t lo x w z ∧
      toLCA t lo y x z ≤ toLCA t lo y w z :=
  ⟨enclosing t lo x w w y z le_rfl (wx.trans xy) yz,
    enclosing t lo y w x z z wx (xy.trans yz) le_rfl⟩

end RotationBST.Geometric.GreedyASS.Reference.Distance
