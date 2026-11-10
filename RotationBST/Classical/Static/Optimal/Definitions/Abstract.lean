module

public import RotationBST.Models.Rotation.Abstract
public import RotationBST.Bounds.LazyFinger.Edges.Definitions.Abstract
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! Optimal static trees by interval dynamic programming. Intervals are
half-open: `[i, j)` holds the keys `i ≤ x < j`. The interval weight `W i j`
is abstract; key weights are the instance `rangeWeight`. The cost of a tree
whose keys are `lo, lo + 1, …` is `LazyFinger.intervalCost W t lo`, the weight
of the interval of every subtree summed over all subtrees; with key weights it
is `∑ₓ wₓ (depth x + 1)` (`Results.weightedCost_eq_intervalCost`). -/
namespace RotationBST.Classical.Static.Optimal

/-- The cubic recurrence `C(i, j) = W(i, j) + min_{i ≤ r < j} (C(i, r) + C(r + 1, j))`,
with `C(i, j) = 0` for an empty interval. -/
def cost (W : Nat → Nat → Nat) (i j : Nat) : Nat :=
  if i < j then
    W i j + ((List.finRange (j - i)).map fun r : Fin (j - i) =>
      cost W i (i + r) + cost W (i + r + 1) j).foldr min (cost W i i + cost W (i + 1) j)
  else 0
termination_by j - i
decreasing_by all_goals omega

/-- The cost of the interval `[i, j)` with root `r`. -/
def candidate (W : Nat → Nat → Nat) (i j r : Nat) : Nat :=
  W i j + cost W i r + cost W (r + 1) j

/-- The largest optimal root of `[i, j)` (Knuth's `R(i, j)`); `i` when the
interval is empty. -/
def root (W : Nat → Nat → Nat) (i j : Nat) : Nat :=
  i + Nat.findGreatest (fun d => candidate W i j (i + d) = cost W i j) (j - i - 1)

/-- The tree built from the largest optimal roots. -/
def tree (W : Nat → Nat → Nat) (i j : Nat) : Tree :=
  if i < j then .node (tree W i (root W i j)) (tree W (root W i j + 1) j) else .nil
termination_by j - i
decreasing_by
  all_goals
    have := Nat.findGreatest_le (P := fun d => candidate W i j (i + d) = cost W i j) (j - i - 1)
    simp only [root]
    omega

/-- The quadrangle inequality `W(i, j) + W(i', j') ≤ W(i', j) + W(i, j')` for
`i ≤ i' ≤ j ≤ j'`. -/
def Quadrangle (W : Nat → Nat → Nat) : Prop :=
  ∀ i i' j j', i ≤ i' → i' ≤ j → j ≤ j' → W i j + W i' j' ≤ W i' j + W i j'

/-- Monotonicity under inclusion: `W(i', j) ≤ W(i, j')` when `[i', j) ⊆ [i, j')`. -/
def InclusionMonotone (W : Nat → Nat → Nat) : Prop :=
  ∀ i i' j j', i ≤ i' → i' ≤ j → j ≤ j' → W i' j ≤ W i j'

/-- Among the roots `lo ≤ r ≤ hi`, the least candidate cost and the largest
root attaining it. Each root examined is one step. -/
def scan (W : Nat → Nat → Nat) (C : Nat → Nat → Nat) (i j lo hi : Nat) : Nat × Nat :=
  (List.range' (lo + 1) (hi - lo)).foldl
    (fun best r => if W i j + C i r + C (r + 1) j ≤ best.1 then (W i j + C i r + C (r + 1) j, r) else best)
    (W i j + C i lo + C (lo + 1) j, lo)

/-- One table entry of Knuth's algorithm, from tables `C`, `K` filled for all
shorter intervals: (cost, root, steps). A single key is its own root; a longer
interval searches only between the roots of its two maximal subintervals. -/
def knuthEntry (W : Nat → Nat → Nat) (C K : Nat → Nat → Nat) (i j : Nat) : Nat × Nat × Nat :=
  if j = i + 1 then (W i j, i, 1)
  else
    let lo := K i (j - 1)
    let hi := K (i + 1) j
    let best := scan W C i j lo hi
    (best.1, best.2, hi + 1 - lo)

/-- Knuth's tables for all intervals of `[0, n)` of length at most `len`, by
increasing length, with the total number of steps. -/
def knuthTables (W : Nat → Nat → Nat) (n : Nat) :
    Nat → (Nat → Nat → Nat) × (Nat → Nat → Nat) × Nat
  | 0 => (fun _ _ => 0, fun i _ => i, 0)
  | len + 1 =>
      let prev := knuthTables W n len
      let entry := fun i => knuthEntry W prev.1 prev.2.1 i (i + len + 1)
      (fun i j => if j = i + len + 1 then (entry i).1 else prev.1 i j,
       fun i j => if j = i + len + 1 then (entry i).2.1 else prev.2.1 i j,
       prev.2.2 + ((List.range (n - len)).map fun i => (entry i).2.2).sum)

/-- Knuth's `O(n²)` algorithm on `[0, n)`: (optimal cost, steps). -/
def knuth (W : Nat → Nat → Nat) (n : Nat) : Nat × Nat :=
  let t := knuthTables W n n
  (t.1 0 n, t.2.2)

end RotationBST.Classical.Static.Optimal

/-! Key weights: `w[x]` is the weight of key `x`, and `0` past the end. -/
namespace RotationBST.Classical.Static

/-- The weighted search cost of a tree: `∑ₓ w[x] · (depth x + 1)`. -/
def weightedCost (w : List Nat) (t : Tree) : Nat :=
  ∑ x ∈ Finset.range t.size, w.getD x 0 * (t.depth x + 1)

/-- The total key weight of the interval `[i, j)`. -/
def rangeWeight (w : List Nat) (i j : Nat) : Nat :=
  ∑ x ∈ Finset.Ico i j, w.getD x 0

/-- The optimal weighted cost over trees on the `w.length` keys, by the recurrence. -/
def optCost (w : List Nat) : Nat := Optimal.cost (rangeWeight w) 0 w.length

/-- An optimal tree, built from the largest optimal roots. -/
def optTree (w : List Nat) : Tree := Optimal.tree (rangeWeight w) 0 w.length

/-- Request counts of the keys `0, …, n - 1`. -/
def counts (n : Nat) (xs : List Nat) : List Nat := (List.range n).map xs.count

end RotationBST.Classical.Static

