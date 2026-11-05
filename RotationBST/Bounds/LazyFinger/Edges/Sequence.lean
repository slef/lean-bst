module

public import RotationBST.Bounds.LazyFinger.Edges.Geometry
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

theorem intervalCost_zero (t : Tree) (lo : Nat) : intervalCost (fun _ _ => 0) t lo = 0 := by
  induction t generalizing lo with
  | nil => rfl
  | node l r ihl ihr => simp [intervalCost, ihl, ihr]

theorem intervalCost_add (u v : Nat → Nat → Nat) (t : Tree) (lo : Nat) :
    intervalCost (fun a b => u a b + v a b) t lo = intervalCost u t lo + intervalCost v t lo := by
  induction t generalizing lo with
  | nil => rfl
  | node l r ihl ihr => simp only [intervalCost, ihl, ihr]; omega

/-- Only tolls on nonempty subtree intervals can affect the objective. -/
theorem intervalCost_congr (u v : Nat → Nat → Nat) (t : Tree) (lo hi : Nat)
    (bound : lo + t.size ≤ hi)
    (h : ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → u a b = v a b) :
    intervalCost u t lo = intervalCost v t lo := by
  induction t generalizing lo with
  | nil => rfl
  | node l r ihl ihr =>
    simp only [intervalCost]
    rw [h lo (lo + (Tree.node l r).size) le_rfl (by omega) bound,
      ihl lo (by simp only [Tree.size] at bound; omega) h,
      ihr (lo + l.size + 1) (by simp only [Tree.size] at bound; omega)
        (fun a b ha hab hb => h a b (by omega) hab hb)]

theorem intervalCost_crossings_cons (t : Tree) (lo p x : Nat) (xs : List Nat) :
    intervalCost (fun a b => crossings a b p (x :: xs)) t lo =
      edgeMovement t lo p x + intervalCost (fun a b => crossings a b x xs) t lo :=
  intervalCost_add _ _ _ _

/-- The edge decomposition preserves normalized lazy-finger cost exactly. -/
theorem costFrom_eq_crossings (t : Tree) (p : Nat) (xs : List Nat)
    (hp : p < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    costFrom t p xs = xs.length + intervalCost (fun a b => crossings a b p xs) t 0 := by
  induction xs generalizing p with
  | nil => simp [costFrom, crossings, intervalCost_zero]
  | cons x xs ih =>
    have hx := valid x (by simp)
    have hv : ∀ y ∈ xs, y < t.size := fun y hy => valid y (by simp [hy])
    rw [costFrom, intervalCost_crossings_cons, ih x hx hv,
      edgeMovement_inside t 0 p x (by omega) (by omega)]
    simp only [Nat.sub_zero, List.length_cons]
    omega

/-- For root initialization, place a virtual initial key just outside the key
universe. Its only extra movement is one traversal of the root's incoming edge.
That constant is independent of the chosen shape, so minimizing these boundary
tolls also minimizes the original root-start cost. -/
theorem cost_eq_crossings (t : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < t.size) :
    cost t xs + (if xs = [] then 0 else 1) =
      xs.length + intervalCost (fun a b => crossings a b t.size xs) t 0 := by
  cases xs with
  | nil => cases t <;> simp [cost, costFrom, crossings, intervalCost_zero]
  | cons x xs =>
    have hx := valid x (by simp)
    have hv : ∀ y ∈ xs, y < t.size := fun y hy => valid y (by simp [hy])
    rw [intervalCost_crossings_cons, edgeMovement_symm,
      edgeMovement_enter t 0 x t.size (by omega) (by omega)]
    have htail := costFrom_eq_crossings t x xs hx hv
    cases t with
    | nil => simp [Tree.size] at hx
    | node l r =>
      simp only [cost, costFrom, distance, lt_self_iff_false, false_and,
        ↓reduceIte, Tree.depth, Nat.sub_zero, List.length_cons,
        List.cons_ne_nil] at *
      omega

end RotationBST.LazyFinger
