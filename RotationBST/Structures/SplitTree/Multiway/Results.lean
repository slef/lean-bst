module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Multiway.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Results

/-- The binary representation has exactly the same keys. -/
theorem encoding (t : Multiway) : t.binary.size = t.size := binary_size t

/-- Balanced 2–3–4 trees have exponentially many keys in their height. -/
theorem balanced_size {h : Nat} {t : Multiway} (valid : Balanced h t) :
    2 ^ h ≤ t.size + 1 ∧ t.size + 1 ≤ 4 ^ h := size_bounds valid

/-- Left sibling repair preserves balance, possibly reducing root height by one,
and uses at most three binary rotations without increasing the node reserve. -/
theorem repair_left {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Rotations t.binary (t.prepareLeft).1.binary (t.prepareLeft).2 ∧
      (t.prepareLeft).2 ≤ 3 ∧ (t.prepareLeft).1.nodes ≤ t.nodes ∧
      (Balanced h (t.prepareLeft).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (t.prepareLeft).1) :=
  ⟨prepareLeft_rotations t, prepareLeft_cost t, prepareLeft_nodes t, valid.prepareLeft⟩

/-- Right sibling repair has the same guarantees, using at most four rotations. -/
theorem repair_right {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Rotations t.binary (t.prepareRight).1.binary (t.prepareRight).2 ∧
      (t.prepareRight).2 ≤ 4 ∧ (t.prepareRight).1.nodes ≤ t.nodes ∧
      (Balanced h (t.prepareRight).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (t.prepareRight).1) :=
  ⟨prepareRight_rotations t, prepareRight_cost t, prepareRight_nodes t, valid.prepareRight⟩

/-- Root merging removes two nodes; the initial number of nodes is at most the
number of keys. These are the reserve facts needed for cascading merges. -/
theorem merge_reserve (a b c d : Multiway) :
    (.four a b c d : Multiway).nodes + 2 = (.two (.two a b) (.two c d) : Multiway).nodes ∧
      (.two (.two a b) (.two c d) : Multiway).nodes ≤ (.two (.two a b) (.two c d) : Multiway).size :=
  ⟨merge_nodes a b c d, nodes_le_size _⟩

end RotationBST.Arboral.Split.Multiway.Results

/-- info: abstract audit passed for `RotationBST.Arboral.Split.Multiway.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Arboral.Split.Multiway.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract]
