module

public import RotationBST.Algorithms.GreedyASS.Reference.Conversion.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract
public import RotationBST.Bounds.StaticTree.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Conversion

theorem population (t : Tree) (nonempty : 0 < t.size) : leaves (convert t) = t.size := by
  induction t with
  | nil => simp [Tree.size] at nonempty
  | node l r ihl ihr =>
    by_cases hl : l.size = 0 <;> by_cases hr : r.size = 0
    · simp [convert, hl, hr, leaves, Tree.size]
    · simp [convert, hl, hr, leaves, ihr (by omega), Tree.size]
    · simp [convert, hl, hr, leaves, ihl (by omega), Tree.size]
    · simp [convert, hl, hr, leaves, ihl (by omega), ihr (by omega), Tree.size, Nat.add_assoc]

/-- Each original descent becomes at most two reference edges, with at
most two extra edges to the leaf representing the destination key. -/
theorem depth (t : Tree) (lo x : Nat) (valid : x < t.size) :
    Distance.depth (convert t) lo (lo + x) ≤ 2 * Tree.depth t x + 2 := by
  induction t generalizing lo x with
  | nil => simp [Tree.size] at valid
  | node l r ihl ihr =>
    have size : x < l.size + r.size + 1 := by simp only [Tree.size] at valid; omega
    by_cases left : x < l.size
    · have hl : l.size ≠ 0 := by omega
      have count := population l (by omega)
      have child := ihl lo x left
      by_cases hr : r.size = 0 <;>
        simpa [convert, hl, hr, Distance.depth, count, Tree.depth, left,
          show lo + x < lo + l.size by omega] using (show
          Distance.depth (convert l) lo (lo + x) + 1 ≤ 2 * (Tree.depth l x + 1) + 2 by omega)
    · by_cases root : x = l.size
      · subst x
        by_cases hl : l.size = 0
        · by_cases hr : r.size = 0 <;> simp [convert, hl, hr, Distance.depth, leaves, Tree.depth]
        · have count := population l (by omega)
          by_cases hr : r.size = 0 <;> simp [convert, hl, hr, Distance.depth, leaves, count, Tree.depth]
      · have right : l.size < x := by omega
        have hr : r.size ≠ 0 := by omega
        have childValid : x - l.size - 1 < r.size := by omega
        have child := ihr (lo + l.size + 1) (x - l.size - 1) childValid
        have key : lo + l.size + 1 + (x - l.size - 1) = lo + x := by omega
        rw [key] at child
        by_cases hl : l.size = 0
        · simp only [hl, Nat.add_zero, Nat.sub_zero] at child
          simp [convert, hl, hr, Distance.depth, leaves, Tree.depth,
            show x ≠ 0 by omega, show ¬lo + x < lo + 1 by omega]
          omega
        · have count := population l (by omega)
          simpa [convert, hl, hr, Distance.depth, leaves, count, Tree.depth, left, root,
            show ¬lo + x < lo + l.size by omega,
            show ¬lo + x < lo + l.size + 1 by omega] using (show
            Distance.depth (convert r) (lo + l.size + 1) (lo + x) + 1 + 1 ≤
              2 * (Tree.depth r (x - l.size - 1) + 1) + 2 by omega)

end RotationBST.Geometric.GreedyASS.Reference.Conversion
