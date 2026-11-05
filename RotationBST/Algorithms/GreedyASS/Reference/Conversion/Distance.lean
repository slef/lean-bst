module

public import RotationBST.Algorithms.GreedyASS.Reference.Conversion.Depth
public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Distance
public import RotationBST.Bounds.LazyFinger.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Conversion

theorem left_edges (l r : Tree) (lo x y : Nat) (hx : x < l.size) (hy : y < l.size) :
    Transitions.edges (convert (.node l r)) lo (lo + x) (lo + y) =
      Transitions.edges (convert l) lo (lo + x) (lo + y) := by
  have hl : l.size ≠ 0 := by omega
  have count := population l (by omega)
  by_cases hr : r.size = 0 <;>
    simp [convert, hl, hr, Transitions.edges, count,
      show lo + x < lo + l.size by omega, show lo + y < lo + l.size by omega]

theorem right_edges (l r : Tree) (lo x y : Nat)
    (hx : l.size < x) (hy : l.size < y) (hr : 0 < r.size) :
    Transitions.edges (convert (.node l r)) lo (lo + x) (lo + y) =
      Transitions.edges (convert r) (lo + l.size + 1) (lo + x) (lo + y) := by
  have nonempty : r.size ≠ 0 := by omega
  by_cases hl : l.size = 0
  · simp [convert, hl, nonempty, Transitions.edges, leaves,
      show lo + 1 ≤ lo + x by omega, show lo + 1 ≤ lo + y by omega,
      show ¬lo + x < lo + 1 by omega]
  · have count := population l (by omega)
    simp [convert, hl, nonempty, Transitions.edges, leaves, count,
      show lo + l.size ≤ lo + x by omega, show lo + l.size ≤ lo + y by omega,
      show ¬lo + x < lo + l.size by omega,
      show lo + l.size + 1 ≤ lo + x by omega, show lo + l.size + 1 ≤ lo + y by omega,
      show ¬lo + x < lo + l.size + 1 by omega]

/-- The conversion gives the upper comparison needed to transfer a
leaf-reference bound to ordinary BSTs. Constants include the endpoint
gadgets; no comparison from the paper is assumed. -/
theorem distance (t : Tree) (lo x y : Nat) (hx : x < t.size) (hy : y < t.size) :
    Transitions.edges (convert t) lo (lo + x) (lo + y) ≤ 2 * LazyFinger.distance t x y + 4 := by
  induction t generalizing lo x y with
  | nil => simp [Tree.size] at hx
  | node l r ihl ihr =>
    by_cases left : x < l.size ∧ y < l.size
    · rw [left_edges l r lo x y left.1 left.2]
      simpa only [LazyFinger.distance, ite_eq_left left] using ihl lo x y left.1 left.2
    · by_cases right : l.size < x ∧ l.size < y
      · have vx : x - l.size - 1 < r.size := by simp only [Tree.size] at hx; omega
        have vy : y - l.size - 1 < r.size := by simp only [Tree.size] at hy; omega
        rw [right_edges l r lo x y right.1 right.2 (by omega)]
        have bound := ihr (lo + l.size + 1) (x - l.size - 1) (y - l.size - 1) vx vy
        have ex : lo + l.size + 1 + (x - l.size - 1) = lo + x := by omega
        have ey : lo + l.size + 1 + (y - l.size - 1) = lo + y := by omega
        simpa only [LazyFinger.distance, ite_eq_right left, ite_eq_left right, ex, ey] using bound
      · have dx := depth (.node l r) lo x hx
        have dy := depth (.node l r) lo y hy
        have path := Transitions.edges_depths (convert (.node l r)) lo (lo + x) (lo + y)
        simp only [LazyFinger.distance, ite_eq_right left, ite_eq_right right]
        omega

end RotationBST.Geometric.GreedyASS.Reference.Conversion
