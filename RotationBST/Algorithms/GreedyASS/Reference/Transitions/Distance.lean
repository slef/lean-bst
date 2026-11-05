module

public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Traces
public import RotationBST.Algorithms.GreedyASS.Reference.Distance.Occurrences
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Transitions

theorem descend_length (t : Tree) (lo searched : Nat) :
    (descend t lo searched).length = Distance.depth t lo searched := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    by_cases left : searched < lo + leaves l <;> simp [descend, Distance.depth, left, il, ir]

theorem ascend_length (t : Tree) (lo searched : Nat) :
    (ascend t lo searched).length = Distance.depth t lo searched := by
  simp [ascend, descend_length]

theorem plan_length (t : Tree) (lo old new : Nat) : (plan t lo old new).length = edges t lo old new := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    by_cases left : old < lo + leaves l ∧ new < lo + leaves l
    · simp only [plan, edges, ite_eq_left left, il]
    · by_cases right : lo + leaves l ≤ old ∧ lo + leaves l ≤ new
      · simp only [plan, edges, ite_eq_right left, ite_eq_left right, ir]
      · simp only [plan, edges, ite_eq_right left, ite_eq_right right, List.length_append,
          ascend_length, descend_length]

theorem edges_depths (t : Tree) (lo x y : Nat) :
    edges t lo x y + 2 * Distance.lcaDepth t lo x y = Distance.depth t lo x + Distance.depth t lo y := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    by_cases left : x < lo + leaves l ∧ y < lo + leaves l
    · have child := il lo
      simp only [edges, Distance.lcaDepth, Distance.depth, ite_eq_left left,
        ite_eq_left left.1, ite_eq_left left.2]
      omega
    · by_cases right : lo + leaves l ≤ x ∧ lo + leaves l ≤ y
      · have child := ir (lo + leaves l)
        simp only [edges, Distance.lcaDepth, Distance.depth, ite_eq_right left,
          ite_eq_left right, ite_eq_right (Nat.not_lt.mpr right.1), ite_eq_right (Nat.not_lt.mpr right.2)]
        omega
      · simp only [edges, Distance.lcaDepth, ite_eq_right left, ite_eq_right right,
          Nat.mul_zero, Nat.add_zero]

theorem plan_repeated (t : Tree) (lo x : Nat) : plan t lo x x = [] := by
  have identity := edges_depths t lo x x
  rw [Distance.self] at identity
  apply List.length_eq_zero_iff.mp
  rw [plan_length]
  omega

/-- The plan length is the actual leaf-to-leaf edge count: add the two
node-counted upward paths and subtract their two copies of the LCA. -/
theorem path_length (t : Tree) (lo x y : Nat)
    (validX : lo ≤ x ∧ x < lo + leaves t) (validY : lo ≤ y ∧ y < lo + leaves t) :
    (plan t lo x y).length + 2 =
      Distance.toRoot (Distance.lca t lo x y) x + Distance.toRoot (Distance.lca t lo x y) y := by
  have identity := edges_depths t lo x y
  obtain ⟨hx, hy⟩ := Distance.lca_contains t lo x y validX validY
  have occurrence := Distance.lca_occurs t lo x y
  have dx := occurrence.depth_eq hx
  have dy := occurrence.depth_eq hy
  rw [plan_length]
  unfold Distance.toRoot
  omega

end RotationBST.Geometric.GreedyASS.Reference.Transitions
