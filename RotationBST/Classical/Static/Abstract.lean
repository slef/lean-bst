module

import RotationBST.Audit.Check
public import RotationBST.Classical.Static.AbstractBridge

@[expose] public section

/-! Static search trees: the balanced tree and the logarithmic baseline.
`Models/Rotation/Abstract` gives the balanced tree `Tree.balanced` and
`Tree.height`; `Bounds/StaticTree/Definitions`
gives the cost of searching a fixed tree; `Bounds/Logarithmic` gives the
baseline `m(1 + log₂ n)`. -/
namespace RotationBST.Classical.Static.Results
open _root_.RotationBST.Tree (height balanced)

/-- The balanced tree has `n` keys (`Tree.balanced_size`). -/
theorem balanced_size (n : Nat) : (balanced n).size = n :=
  Tree.balanced_size n

/-- Every key of the balanced tree lies at depth at most `⌊log₂ n⌋`. -/
theorem balanced_depth (n x : Nat) (hx : x < n) : (balanced n).depth x ≤ Nat.log2 n :=
  Static.balanced_depth n x hx

/-- Conversely, every nonempty tree has a key at depth at least `⌊log₂ n⌋`. -/
theorem exists_deep (t : Tree) (h : 0 < t.size) :
    ∃ x < t.size, Nat.log2 t.size ≤ t.depth x :=
  Static.exists_deep t h

/-- Searching the balanced tree costs at most `1 + ⌊log₂ n⌋` per request. -/
theorem balanced_cost (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    StaticTree.cost (balanced n) xs ≤ xs.length * (Nat.log2 n + 1) :=
  Static.balanced_cost n xs valid

/-- The same bound against the real-valued baseline. -/
theorem balanced_cost_le_logCost (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (StaticTree.cost (balanced n) xs : ℝ) ≤ Bounds.logCost n xs :=
  Static.balanced_cost_le_logCost n xs valid

/-- No static tree does better in the worst case: repeating a deepest key `m`
times costs at least `m(1 + ⌊log₂ n⌋)`. -/
theorem exists_expensive (t : Tree) (h : 0 < t.size) (m : Nat) :
    ∃ x < t.size, m * (Nat.log2 t.size + 1) ≤ StaticTree.cost t (List.replicate m x) :=
  Static.exists_expensive t h m

/-- The balanced tree has height `⌊log₂ n⌋ + 1`… -/
theorem balanced_height_eq (n : Nat) (h : 0 < n) : height (balanced n) = Nat.log2 n + 1 :=
  Static.balanced_height_eq n h

/-- …the minimum: every nonempty tree has height at least `⌊log₂ n⌋ + 1`. -/
theorem log2_add_one_le_height (t : Tree) (h : 0 < t.size) : Nat.log2 t.size + 1 ≤ height t :=
  Static.log2_add_one_le_height t h

end RotationBST.Classical.Static.Results

/-- info: abstract audit passed for `RotationBST.Classical.Static.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Classical.Static.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.Logarithmic.Abstract]
