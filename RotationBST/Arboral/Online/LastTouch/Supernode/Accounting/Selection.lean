module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Accounting.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Assembly.Selection
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Lifetime.Proofs

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- Materializing a split hierarchy preserves every child's credit exactly,
while the old parent credit becomes the credit of its surviving intervals. -/
theorem assemblePartition_credit (parts : Partitioned) (children : List Nested) (first : Nat)
    (fits : first + parts.tree.size + 1 ≤ children.length) :
    (assemblePartition parts children first).credit = parts.credit +
      (((children.drop first).take (parts.tree.size + 1)).map Nested.credit).sum := by
  induction parts generalizing first with
  | leaf interval =>
    cases interval with
    | none =>
      have inside : first < children.length := by
        simp only [Partitioned.tree, intervalTree, Tree.size] at fits
        omega
      simp only [assemblePartition, Assembly.credit, List.getElem?_eq_getElem inside, Option.getD_some,
        Partitioned.credit, intervalCredit, intervalNodes, intervalTree, Tree.size,
        Partitioned.tree]
      simp [List.take_one, List.head?_drop, List.getElem?_eq_getElem inside]
    | some state =>
      simp only [assemblePartition, Assembly.credit, retainedNested, Nested.credit,
        Partitioned.credit, Partitioned.tree, intervalTree, state_size]
  | branch left right il ir =>
    have leftFits : first + left.tree.size + 1 ≤ children.length := by
      simp only [Partitioned.tree, Tree.size] at fits; omega
    have rightFits : first + left.tree.size + 1 + right.tree.size + 1 ≤ children.length := by
      simp only [Partitioned.tree, Tree.size] at fits; omega
    simp only [assemblePartition, Assembly.credit, Partitioned.credit,
      il first leftFits, ir (first + left.tree.size + 1) rightFits, Partitioned.tree, Tree.size]
    rw [show left.tree.size + 1 + right.tree.size + 1 = (left.tree.size + 1) + (right.tree.size + 1) by omega,
      List.take_add (i := left.tree.size + 1) (j := right.tree.size + 1),
      List.map_append, List.sum_append, List.drop_drop]
    simp only [← Nat.add_assoc]
    omega

/-- Selection spends existing parent credit and preserves child credit; it
does not allocate a fresh per-row allowance to surviving intervals. -/
theorem selectParent_credit {P : Finset Point} {lo : Nat} {state : State} {children : List Nested}
    (represented : Represents P lo (.layer state children)) (keys : Finset Nat) :
    (selectParent state children lo keys).2 + (selectParent state children lo keys).1.credit ≤
      (Nested.layer state children).credit := by
  have balanced : state.HeightValid := by cases represented; assumption
  have arity : children.length = state.size + 1 := by cases represented; assumption
  let ranks := touchedRanks state.tree.size
    (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 lo keys
  have bounds : ∀ key ∈ ranks, key < (intervalTree (some state)).size := by
    intro key member
    exact Finset.mem_range.mp (Finset.mem_filter.mp member).1
  have applicable := selectionPlan_applicable (ranks.sort (· ≤ ·)) (some state) 0 balanced
    ranks.sortedLT_sort.pairwise (by
      intro key member
      exact ⟨Nat.zero_le _, by simpa only [Nat.zero_add] using bounds key ((Finset.mem_sort (· ≤ ·)).mp member)⟩)
  have budget := runPlan_budget _ (some state) balanced applicable
  have spec := selectKeys_spec (some state) ranks balanced bounds
  have size : (selectKeys (some state) ranks).1.tree.size = state.size := by
    simpa only [intervalTree, state_size] using spec.2.1.size_eq.symm
  have materialized := assemblePartition_credit (selectKeys (some state) ranks).1 children 0 (by omega)
  rw [size, ← arity] at materialized
  simp only [List.drop_zero, List.take_length] at materialized
  change (selectKeys (some state) ranks).2 + (assemblePartition (selectKeys (some state) ranks).1 children 0).credit ≤ _
  rw [materialized]
  simp only [Nested.credit]
  change (selectKeys (some state) ranks).2 + (selectKeys (some state) ranks).1.credit ≤ _ at budget
  omega

end RotationBST.Arboral.Online.Supernode
