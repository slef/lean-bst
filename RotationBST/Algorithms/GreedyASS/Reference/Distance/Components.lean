module

public import RotationBST.Algorithms.GreedyASS.Reference.Distance.Occurrences
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Distance

/-- For a component containing an intermediate leaf, the enclosing LCA is
at or below its root exactly when both endpoints lie in that component. -/
theorem Occurs.encloses_iff {t : Tree} {lo k a x b : Nat} {c : Component}
    (occurs : Occurs t lo c k) (inside : c.Contains x) (ax : a ≤ x) (xb : x ≤ b)
    (validA : lo ≤ a ∧ a < lo + leaves t) (validB : lo ≤ b ∧ b < lo + leaves t) :
    k ≤ lcaDepth t lo a b ↔ c.Contains a ∧ c.Contains b := by
  induction occurs generalizing a x b with
  | root t lo =>
    constructor
    · intro _
      exact ⟨validA, validB⟩
    · intro _
      exact Nat.zero_le _
  | @left l r lo c k h ih =>
    have vx := h.valid inside
    have aleft : a < lo + leaves l := by omega
    by_cases bleft : b < lo + leaves l
    · simp only [lcaDepth, ite_eq_left (And.intro aleft bleft), Nat.add_le_add_iff_right]
      exact ih inside ax xb ⟨validA.1, aleft⟩ ⟨validB.1, bleft⟩
    · have notLeft : ¬ (a < lo + leaves l ∧ b < lo + leaves l) := by omega
      have notRight : ¬ (lo + leaves l ≤ a ∧ lo + leaves l ≤ b) := by omega
      simp only [lcaDepth, ite_eq_right notLeft, ite_eq_right notRight]
      constructor
      · omega
      · rintro ⟨_, hb⟩
        have := h.valid hb
        omega
  | @right l r lo c k h ih =>
    have vx := h.valid inside
    have bright : lo + leaves l ≤ b := by omega
    by_cases aright : lo + leaves l ≤ a
    · have notLeft : ¬ (a < lo + leaves l ∧ b < lo + leaves l) := by omega
      simp only [lcaDepth, ite_eq_right notLeft, ite_eq_left (And.intro aright bright), Nat.add_le_add_iff_right]
      apply ih inside ax xb
      · simp only [leaves] at validA
        exact ⟨aright, by omega⟩
      · simp only [leaves] at validB
        exact ⟨bright, by omega⟩
    · have notLeft : ¬ (a < lo + leaves l ∧ b < lo + leaves l) := by omega
      have notRight : ¬ (lo + leaves l ≤ a ∧ lo + leaves l ≤ b) := by omega
      simp only [lcaDepth, ite_eq_right notLeft, ite_eq_right notRight]
      constructor
      · omega
      · rintro ⟨ha, _⟩
        have := h.valid ha
        omega

/-- Geometric comparison underlying Fact 3.2, before assigning any colors
or applying the special top-corner rule. -/
theorem Occurs.compare {t : Tree} {lo k a x b : Nat} {c : Component}
    (occurs : Occurs t lo c k) (inside : c.Contains x) (ax : a ≤ x) (xb : x ≤ b)
    (validA : lo ≤ a ∧ a < lo + leaves t) (validB : lo ≤ b ∧ b < lo + leaves t) :
    toLCA t lo x a b ≤ toRoot c x ↔ c.Contains a ∧ c.Contains b := by
  have height := occurs.depth_eq inside
  have enclosing := occurs.encloses_iff inside ax xb validA validB
  rw [← enclosing]
  unfold toLCA toRoot
  rw [height]
  omega

theorem forest_compare (t : Tree) (lo searched a x b : Nat) {c : Component}
    (member : c ∈ forest t lo searched) (inside : c.Contains x) (ax : a ≤ x) (xb : x ≤ b)
    (validA : lo ≤ a ∧ a < lo + leaves t) (validB : lo ≤ b ∧ b < lo + leaves t) :
    toLCA t lo x a b ≤ toRoot c x ↔ c.Contains a ∧ c.Contains b := by
  obtain ⟨k, occurrence⟩ := forest_occurs t lo searched member
  exact occurrence.compare inside ax xb validA validB

theorem forest_outside (t : Tree) (lo searched a x b : Nat) {c : Component}
    (member : c ∈ forest t lo searched) (inside : c.Contains x) (ax : a ≤ x) (xb : x ≤ b)
    (validA : lo ≤ a ∧ a < lo + leaves t) (validB : lo ≤ b ∧ b < lo + leaves t) :
    toRoot c x < toLCA t lo x a b ↔ ¬ c.Contains a ∨ ¬ c.Contains b := by
  have comparison := forest_compare t lo searched a x b member inside ax xb validA validB
  rw [← Nat.not_le, comparison, not_and_or]

/-- Moving a component root to its parent adds exactly one to the upward
node-counted distance; this is the distance change used in Phase I. -/
theorem merge_left (l r : Tree) (lo x : Nat) (inside : lo ≤ x ∧ x < lo + leaves l) :
    toRoot ⟨lo, .node l r⟩ x = toRoot ⟨lo, l⟩ x + 1 := by
  simp only [toRoot, depth, ite_eq_left inside.2]

theorem merge_right (l r : Tree) (lo x : Nat)
    (inside : lo + leaves l ≤ x ∧ x < lo + leaves l + leaves r) :
    toRoot ⟨lo, .node l r⟩ x = toRoot ⟨lo + leaves l, r⟩ x + 1 := by
  simp only [toRoot, depth, ite_eq_right (Nat.not_lt.mpr inside.1)]

end RotationBST.Geometric.GreedyASS.Reference.Distance
