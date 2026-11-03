module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Select.Defs
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Partial.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger.TwoEnded

/-- Every selected rank is legal in its recursively shortened interval. -/
theorem selectionPlan_applicable (keys : List Nat) (input : Option State) (offset : Nat)
    (valid : IntervalValid input) (ordered : keys.Pairwise (· < ·))
    (bounds : ∀ key ∈ keys, offset ≤ key ∧ key < offset + (intervalTree input).size) :
    (selectionPlan offset keys).Applicable input := by
  induction keys generalizing input offset with
  | nil => trivial
  | cons key keys ih =>
    have current := bounds key (List.mem_cons_self ..)
    have order := List.pairwise_cons.mp ordered
    cases input with
    | none => simp only [intervalTree, Tree.size] at current; omega
    | some state =>
      have existsKey : key - offset < state.size := by
        simp only [intervalTree, state_size] at current
        omega
      have sizes := split_sizes valid (key - offset) existsKey
      have good := split_valid valid (key - offset) existsKey
      refine ⟨existsKey, trivial, ih _ _ good.2 order.2 ?_⟩
      intro next member
      have larger := order.1 next member
      have inside := bounds next (List.mem_cons_of_mem _ member)
      simp only [intervalTree, state_size] at current inside
      rw [sizes.2]
      omega

/-- Selection exposes precisely the supplied ranks, without exposing any key
inside a retained interval. -/
theorem selectionPlan_keys (keys : List Nat) (input : Option State) (offset : Nat)
    (valid : IntervalValid input) (ordered : keys.Pairwise (· < ·))
    (bounds : ∀ key ∈ keys, offset ≤ key ∧ key < offset + (intervalTree input).size) :
    (runPlan (selectionPlan offset keys) input).1.keys offset = keys := by
  induction keys generalizing input offset with
  | nil => rfl
  | cons key keys ih =>
    have current := bounds key (List.mem_cons_self ..)
    have order := List.pairwise_cons.mp ordered
    cases input with
    | none => simp only [intervalTree, Tree.size] at current; omega
    | some state =>
      have existsKey : key - offset < state.size := by
        simp only [intervalTree, state_size] at current
        omega
      have sizes := split_sizes valid (key - offset) existsKey
      have good := split_valid valid (key - offset) existsKey
      have nextBounds : ∀ next ∈ keys, key + 1 ≤ next ∧
          next < key + 1 + (intervalTree (split state (key - offset)).right).size := by
        intro next member
        have larger := order.1 next member
        have inside := bounds next (List.mem_cons_of_mem _ member)
        simp only [intervalTree, state_size] at current inside
        rw [sizes.2]
        omega
      have tail := ih (split state (key - offset)).right (key + 1) good.2 order.2 nextBounds
      simp only [selectionPlan, runPlan, Partitioned.keys, Partitioned.tree, List.nil_append]
      rw [sizes.1, show offset + (key - offset) = key by omega]
      exact congrArg (List.cons key) tail

/-- A finite touch set supplies its own sorted, duplicate-free split plan. -/
theorem selectKeys_spec (input : Option State) (keys : Finset Nat) (valid : IntervalValid input)
    (bounds : ∀ key ∈ keys, key < (intervalTree input).size) :
    (selectKeys input keys).1.Valid ∧
      Rotations (intervalTree input) (selectKeys input keys).1.tree (selectKeys input keys).2 ∧
      (selectKeys input keys).1.keys 0 = keys.sort (· ≤ ·) ∧
      (selectKeys input keys).2 + 14 * (selectKeys input keys).1.reserve ≤
        6014 * (intervalTree input).size := by
  have ordered : (keys.sort (· ≤ ·)).Pairwise (· < ·) := keys.sortedLT_sort.pairwise
  have inside : ∀ key ∈ keys.sort (· ≤ ·), 0 ≤ key ∧ key < 0 + (intervalTree input).size := by
    intro key member
    exact ⟨Nat.zero_le _, by simpa using bounds key ((Finset.mem_sort (· ≤ ·)).mp member)⟩
  have applicable := selectionPlan_applicable _ input 0 valid ordered inside
  have result := runPlan_spec _ input valid applicable
  exact ⟨result.1, result.2, selectionPlan_keys _ input 0 valid ordered inside,
    runPlan_linear _ input valid applicable⟩

end RotationBST.Geometric.Split.Multiway.Finger.TwoEnded
