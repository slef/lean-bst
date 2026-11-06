module

public import RotationBST.Bounds.LazyFinger.WalkMetric
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger
open Pointer

private theorem depth_right (l t : Tree) (x : Nat) :
    Tree.depth (.node l t) (l.size + 1 + x) = Tree.depth t x + 1 := by
  have low : ¬ l.size + 1 + x < l.size := by omega
  have different : l.size + 1 + x ≠ l.size := by omega
  have index : l.size + 1 + x - l.size - 1 = x := by omega
  simp only [Tree.depth, low, different, ↓reduceIte, index]

/-- From outside a subtree, differences in distance to its nodes are exactly
their differences in depth below its root. -/
theorem distance_outside_context (cs : List Frame) (t : Tree) (x z y : Nat)
    (hx : x < t.size) (hz : z < t.size) (hy : y < (plug cs t).size)
    (outside : ¬ (offset cs ≤ y ∧ y < offset cs + t.size)) :
    distance (plug cs t) (offset cs + x) y + Tree.depth t z =
      distance (plug cs t) (offset cs + z) y + Tree.depth t x := by
  induction cs generalizing t x z with
  | nil => simp only [plug, offset] at hy outside; omega
  | cons frame cs ih =>
    cases frame with
    | left r =>
      have px : x < (Tree.node t r).size := by simp only [Tree.size]; omega
      have pz : z < (Tree.node t r).size := by simp only [Tree.size]; omega
      simp only [plug, offset] at hy outside ⊢
      by_cases inside : offset cs ≤ y ∧ y < offset cs + (Tree.node t r).size
      · have localY : y - offset cs < (Tree.node t r).size := by omega
        have shifted : y = offset cs + (y - offset cs) := by omega
        have other : ¬ y - offset cs < t.size := by omega
        rw [shifted, distance_plug cs _ _ _ px localY, distance_plug cs _ _ _ pz localY]
        simp only [distance, other, and_false, Nat.not_lt.mpr hx.le, Nat.not_lt.mpr hz.le,
          false_and, ↓reduceIte, Tree.depth, hx, hz]
        omega
      · have outer := ih (.node t r) x z px pz hy inside
        simp only [Tree.depth, hx, hz, ↓reduceIte] at outer
        omega
    | right l =>
      have px : l.size + 1 + x < (Tree.node l t).size := by simp only [Tree.size]; omega
      have pz : l.size + 1 + z < (Tree.node l t).size := by simp only [Tree.size]; omega
      have sx : offset cs + l.size + 1 + x = offset cs + (l.size + 1 + x) := by omega
      have sz : offset cs + l.size + 1 + z = offset cs + (l.size + 1 + z) := by omega
      simp only [plug, offset] at hy outside ⊢
      rw [sx, sz]
      by_cases inside : offset cs ≤ y ∧ y < offset cs + (Tree.node l t).size
      · have localY : y - offset cs < (Tree.node l t).size := by omega
        have shifted : y = offset cs + (y - offset cs) := by omega
        have other : ¬ l.size < y - offset cs := by simp only [Tree.size] at inside; omega
        have lowX : ¬ l.size + 1 + x < l.size := by omega
        have lowZ : ¬ l.size + 1 + z < l.size := by omega
        rw [shifted, distance_plug cs _ _ _ px localY, distance_plug cs _ _ _ pz localY]
        simp only [distance, lowX, lowZ, other, and_false, false_and, ↓reduceIte, depth_right]
        omega
      · have outer := ih (.node l t) (l.size + 1 + x) (l.size + 1 + z) px pz hy inside
        simp only [depth_right] at outer
        omega

/-- The left child is the next shortest-path step for targets in its interval. -/
theorem down_left_closer (a b r : Tree) (cs : List Frame) (y : Nat) (valid : y < (Tree.node a b).size) :
    distance (plug cs (.node (.node a b) r)) (offset cs + a.size) (offset cs + y) + 1 =
      distance (plug cs (.node (.node a b) r)) (offset cs + (Tree.node a b).size) (offset cs + y) := by
  have upper : y < a.size + b.size + 1 := by simp only [Tree.size] at valid; omega
  rw [distance_plug cs _ _ _ (by simp only [Tree.size]; omega) (by simp only [Tree.size]; omega),
    distance_plug cs _ _ _ (by simp only [Tree.size]; omega) (by simp only [Tree.size]; omega)]
  have child : a.size < (Tree.node a b).size := by simp only [Tree.size]; omega
  rw [distance_from_root]
  rw [distance, ite_eq_left ⟨child, valid⟩, distance_from_root]
  simp only [Tree.depth, valid, ↓reduceIte]

theorem down_right_closer (l a b : Tree) (cs : List Frame) (y : Nat) (valid : y < (Tree.node a b).size) :
    distance (plug cs (.node l (.node a b))) (offset cs + (l.size + 1 + a.size))
        (offset cs + (l.size + 1 + y)) + 1 =
      distance (plug cs (.node l (.node a b))) (offset cs + l.size) (offset cs + (l.size + 1 + y)) := by
  have upper : y < a.size + b.size + 1 := by simp only [Tree.size] at valid; omega
  rw [distance_plug cs _ _ _ (by simp only [Tree.size]; omega) (by simp only [Tree.size]; omega),
    distance_plug cs _ _ _ (by simp only [Tree.size]; omega) (by simp only [Tree.size]; omega)]
  have leftA : ¬ l.size + 1 + a.size < l.size := by omega
  have highA : l.size < l.size + 1 + a.size := by omega
  have highY : l.size < l.size + 1 + y := by omega
  have indexA : l.size + 1 + a.size - l.size - 1 = a.size := by omega
  have indexY : l.size + 1 + y - l.size - 1 = y := by omega
  rw [distance_from_root]
  rw [distance, ite_eq_right (by simp only [leftA, false_and, not_false_eq_true]),
    ite_eq_left ⟨highA, highY⟩, indexA, indexY, distance_from_root, depth_right]

/-- A target outside a left child's interval is reached through its parent. -/
theorem up_left_closer (a b r : Tree) (cs : List Frame) (y : Nat)
    (valid : y < (plug cs (.node (.node a b) r)).size)
    (outside : ¬ (offset cs ≤ y ∧ y < offset cs + (Tree.node a b).size)) :
    distance (plug cs (.node (.node a b) r)) (offset cs + (Tree.node a b).size) y + 1 =
      distance (plug cs (.node (.node a b) r)) (offset cs + a.size) y := by
  have child : a.size < (Tree.node a b).size := by simp only [Tree.size]; omega
  have px : a.size < (Tree.node (.node a b) r).size := by simp only [Tree.size]; omega
  have pz : (Tree.node a b).size < (Tree.node (.node a b) r).size := by simp only [Tree.size]; omega
  by_cases inside : offset cs ≤ y ∧ y < offset cs + (Tree.node (.node a b) r).size
  · have localY : y - offset cs < (Tree.node (.node a b) r).size := by omega
    have shifted : y = offset cs + (y - offset cs) := by omega
    have other : ¬ y - offset cs < (Tree.node a b).size := by omega
    rw [shifted, distance_plug cs _ _ _ pz localY, distance_plug cs _ _ _ px localY, distance_from_root]
    have high : ¬ (Tree.node a b).size < a.size := by omega
    rw [distance, ite_eq_right (by simp only [other, and_false, not_false_eq_true]),
      ite_eq_right (by simp only [high, false_and, not_false_eq_true])]
    simp [Tree.depth, child, Nat.add_comm]
  · have comparison := distance_outside_context cs (.node (.node a b) r) a.size (Tree.node a b).size y px pz valid inside
    have zero : Tree.depth (.node (.node a b) r) (Tree.node a b).size = 0 := by simp [Tree.depth]
    have one : Tree.depth (.node (.node a b) r) a.size = 1 := by simp [Tree.depth, child]
    rw [zero, one] at comparison
    omega

theorem up_right_closer (l a b : Tree) (cs : List Frame) (y : Nat)
    (valid : y < (plug cs (.node l (.node a b))).size)
    (outside : ¬ (offset cs + l.size + 1 ≤ y ∧ y < offset cs + l.size + 1 + (Tree.node a b).size)) :
    distance (plug cs (.node l (.node a b))) (offset cs + l.size) y + 1 =
      distance (plug cs (.node l (.node a b))) (offset cs + (l.size + 1 + a.size)) y := by
  have px : l.size + 1 + a.size < (Tree.node l (.node a b)).size := by simp only [Tree.size]; omega
  have pz : l.size < (Tree.node l (.node a b)).size := by simp only [Tree.size]; omega
  by_cases inside : offset cs ≤ y ∧ y < offset cs + (Tree.node l (.node a b)).size
  · have localY : y - offset cs < (Tree.node l (.node a b)).size := by omega
    have shifted : y = offset cs + (y - offset cs) := by omega
    have other : ¬ l.size < y - offset cs := by simp only [Tree.size] at inside outside; omega
    have low : ¬ l.size + 1 + a.size < l.size := by omega
    rw [shifted, distance_plug cs _ _ _ pz localY, distance_plug cs _ _ _ px localY, distance_from_root]
    rw [distance, ite_eq_right (by simp only [low, false_and, not_false_eq_true]),
      ite_eq_right (by simp only [other, and_false, not_false_eq_true]), depth_right]
    simp [Tree.depth, Nat.add_comm]
  · have comparison := distance_outside_context cs (.node l (.node a b)) (l.size + 1 + a.size) l.size y px pz valid inside
    have zero : Tree.depth (.node l (.node a b)) l.size = 0 := by simp [Tree.depth]
    have one : Tree.depth (.node l (.node a b)) (l.size + 1 + a.size) = 1 := by rw [depth_right]; simp [Tree.depth]
    rw [zero, one] at comparison
    omega

end RotationBST.LazyFinger
