module

public import RotationBST.Bounds.StaticTree.Trace.Invariant
public import RotationBST.Models.Pointer.Invariant.Mirror
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.StaticTree.Trace
open _root_.RotationBST.Tree (depth)

private theorem depth_right {l r : Tree} {x : Nat} (right : l.size < x) :
    depth (.node l r) x = depth r (x - l.size - 1) + 1 := by
  rw [depth, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Reflection preserves search depth at the reflected existing rank. -/
theorem mirror_rank_depth (t : Tree) (x : Nat) (inside : x < t.size) :
    depth t.mirror (t.size - 1 - x) = depth t x := by
  induction t generalizing x with
  | nil => simp [Tree.size] at inside
  | node l r il ir =>
    by_cases left : x < l.size
    · have index : (l.size + 1 + r.size - 1 - x) - r.size - 1 = l.size - 1 - x := by omega
      have outside : ¬ l.size + 1 + r.size - 1 - x < r.size := by omega
      have different : ¬ l.size + 1 + r.size - 1 - x = r.size := by omega
      simpa only [Tree.mirror, Tree.size, depth, Tree.mirror_size,
        ite_eq_left left, ite_eq_right outside, ite_eq_right different, index] using congrArg (· + 1) (il x left)
    · by_cases root : x = l.size
      · subst x
        simp [Tree.mirror, depth, Tree.size, Tree.mirror_size]
      · have valid : x - l.size - 1 < r.size := by simp only [Tree.size] at inside; omega
        have index : l.size + 1 + r.size - 1 - x = r.size - 1 - (x - l.size - 1) := by omega
        have before : l.size + 1 + r.size - 1 - x < r.size := by omega
        have reflected : r.size - 1 - (x - l.size - 1) < r.size := by omega
        simpa only [Tree.mirror, Tree.size, depth, Tree.mirror_size,
          ite_eq_right left, ite_eq_right root, ite_eq_left before, index, ite_eq_left reflected] using
          congrArg (· + 1) (ir (x - l.size - 1) valid)

/-- Totalized out-of-range searches all follow the same rightmost branch. -/
theorem depth_above_size (t : Tree) (x : Nat) (past : t.size ≤ x) : depth t x = depth t t.size := by
  induction t generalizing x with
  | nil => rfl
  | node l r _ ir =>
    have next : r.size ≤ x - l.size - 1 := by simp only [Tree.size] at past; omega
    rw [depth_right (x := x) (by simp only [Tree.size] at past; omega),
      depth_right (x := (Tree.node l r).size) (by simp only [Tree.size]; omega)]
    have index : (Tree.node l r).size - l.size - 1 = r.size := by simp only [Tree.size]; omega
    rw [index]
    exact congrArg (· + 1) (ir _ next)

/-- The first missing rank lies one edge below the largest existing key. -/
theorem depth_boundary (t : Tree) (live : t ≠ .nil) : depth t t.size = depth t (t.size - 1) + 1 := by
  induction t with
  | nil => exact False.elim (live rfl)
  | node l r _ ir =>
    cases r with
    | nil => simp [depth, Tree.size]
    | node a b =>
      have lower : l.size < (Tree.node l (.node a b)).size - 1 := by simp only [Tree.size]; omega
      have index : (Tree.node l (.node a b)).size - 1 - l.size - 1 = (Tree.node a b).size - 1 := by
        simp only [Tree.size]; omega
      have ih := ir (by intro h; cases h)
      rw [depth_right (l := l) (r := .node a b) (x := (Tree.node l (.node a b)).size)
        (by simp only [Tree.size]; omega),
        depth_right (l := l) (r := .node a b) lower, index]
      have edge : (Tree.node l (.node a b)).size - l.size - 1 = (Tree.node a b).size := by
        simp only [Tree.size]; omega
      rw [edge]
      omega

/-- Pointwise depth comparisons transfer through reflection, including the
out-of-range values of the totalized depth function. -/
theorem mirror_bound {s t : Tree} {factor constant : Nat} (factorPositive : 1 ≤ factor)
    (size : t.size = s.size) (bound : ∀ x, depth t x ≤ factor * depth s x + constant) :
    ∀ x, depth t.mirror x ≤ factor * depth s.mirror x + constant := by
  have validBound : ∀ x, x < s.size → depth t.mirror x ≤ factor * depth s.mirror x + constant := by
    intro x inside
    have reflected : s.size - 1 - x < s.size := by omega
    have back : s.size - 1 - (s.size - 1 - x) = x := by omega
    have first := mirror_rank_depth t (s.size - 1 - x) (by omega)
    have last := mirror_rank_depth s (s.size - 1 - x) reflected
    rw [size, back] at first
    rw [back] at last
    rw [first, last]
    exact bound _
  intro x
  by_cases inside : x < s.size
  · exact validBound x inside
  · by_cases empty : s = .nil
    · subst s
      have emptyT : t = .nil := by cases t <;> simp_all [Tree.size]
      subst t
      simp [Tree.mirror, depth]
    · have nonempty : 0 < s.size := by cases s <;> simp_all [Tree.size]
      have liveT : t.mirror ≠ .nil := by
        intro nil
        have sizes := congrArg Tree.size nil
        simp only [Tree.mirror_size, Tree.size, size] at sizes
        omega
      have liveS : s.mirror ≠ .nil := by
        intro nil
        have sizes := congrArg Tree.size nil
        simp only [Tree.mirror_size, Tree.size] at sizes
        omega
      rw [depth_above_size t.mirror x (by simpa only [Tree.mirror_size, size] using (Nat.le_of_not_gt inside)),
        depth_above_size s.mirror x (by simpa only [Tree.mirror_size] using (Nat.le_of_not_gt inside)),
        depth_boundary _ liveT, depth_boundary _ liveS]
      simp only [Tree.mirror_size, size]
      have last := validBound (s.size - 1) (by omega)
      nlinarith

/-- Reflect a structural depth certificate while keeping the same constants
and cost. Rank identities are reflected together with the physical tree. -/
theorem within_mirror_depth {a b : Pointer.Config} {cost factor constant : Nat}
    (factorPositive : 1 ≤ factor)
    (h : Pointer.TraceWithin (fun t => t.size = a.tree.size ∧
      ∀ x, depth t x ≤ factor * depth a.tree x + constant) a b cost) :
    Pointer.TraceWithin (fun t => t.size = a.mirror.tree.size ∧
      ∀ x, depth t x ≤ factor * depth a.mirror.tree x + constant) a.mirror b.mirror cost := by
  apply h.mirror.weaken
  intro t bound
  refine ⟨?_, ?_⟩
  · simpa only [Pointer.Config.mirror_tree, Tree.mirror_size] using bound.1
  · have reflected := mirror_bound factorPositive bound.1 bound.2
    simpa only [Tree.mirror_mirror, Pointer.Config.mirror_tree] using reflected

end RotationBST.StaticTree.Trace
