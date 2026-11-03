module

public import RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs
public import RotationBST.Structures.SplitTree.Multiway.Join.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Join

theorem compact_rotations (hl hr : Nat) (l r : Multiway) :
    Rotations (.node l.binary r.binary) (compact hl hr l r).tree.binary (compact hl hr l r).cost := by
  by_cases eq : hl = hr
  · cases l <;> cases r <;> simp only [compact, eq, ite_true] <;>
      first | exact .refl | exact run_rotations _ _ _ _
  · simpa only [compact, eq, ite_false] using run_rotations hl hr l r

theorem compact_cost (hl hr : Nat) (l r : Multiway) :
    (compact hl hr l r).cost ≤ 3 * (hl - hr + (hr - hl)) := by
  by_cases eq : hl = hr
  · cases l <;> cases r <;> simp only [compact, eq, ite_true] <;>
      first | exact Nat.zero_le _ | exact run_cost _ _ _ _
  · simpa only [compact, eq, ite_false] using run_cost hl hr l r

theorem compact_balance {hl hr : Nat} {l r : Multiway} (left : Balanced hl l) (right : Balanced hr r) :
    Balanced (compact hl hr l r).height (compact hl hr l r).tree ∧
      max hl hr ≤ (compact hl hr l r).height ∧ (compact hl hr l r).height ≤ max hl hr + 1 := by
  by_cases eq : hl = hr
  · subst hr
    cases l <;> cases r <;> simp only [compact, ite_true] <;>
      try exact run_balance left right
    cases left with
    | two ha hb =>
      cases right with
      | two hc hd => exact ⟨.four ha hb hc hd, by simp, by simp⟩
  · simpa only [compact, eq, ite_false] using run_balance left right

theorem compact_size (hl hr : Nat) (l r : Multiway) :
    (compact hl hr l r).tree.size = l.size + 1 + r.size := by
  have sizes := (compact_rotations hl hr l r).size_eq
  simpa only [Tree.size, binary_size] using sizes.symm

end RotationBST.Geometric.Split.Multiway.Join
