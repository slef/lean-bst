module

public import RotationBST.Structures.SplitTree.Multiway.Extract.Balance

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway

private theorem descendFirst_cost (recur : Multiway → Multiway × Nat) {h : Nat} {t : Multiway}
    (valid : Balanced h t) (nonempty : t ≠ .nil)
    (recursive : ∀ child k, child.nodes < t.nodes → Balanced k child → (recur child).2 ≤ 7 * k) :
    (descendFirst recur t).2 + 5 ≤ 7 * h := by
  cases valid with
  | nil => contradiction
  | @two k l r ha hb =>
    have bound := recursive l k (by simp only [nodes]; omega) ha
    by_cases empty : l = .nil <;> simp only [descendFirst, empty, ite_true, ite_false] <;> omega
  | @three k l m r ha hb hc =>
    have bound := recursive l k (by simp only [nodes]; omega) ha
    by_cases empty : l = .nil <;> simp only [descendFirst, empty, ite_true, ite_false] <;> omega
  | @four k a b c d ha hb hc hd =>
    have bound := recursive a k (by simp only [nodes]; omega) ha
    by_cases empty : a = .nil <;> simp only [descendFirst, empty, ite_true, ite_false] <;> omega

/-- This ordinary root-based extraction takes at most seven rotations per level.
The stronger smaller-side finger bound is a separate split-tree obligation. -/
theorem extractMinAux_cost (fuel : Nat) {h : Nat} {t : Multiway}
    (valid : Balanced h t) (enough : t.nodes < fuel) : (extractMinAux fuel t).2 ≤ 7 * h := by
  induction fuel generalizing h t with
  | zero => omega
  | succ fuel ih =>
    by_cases empty : t = .nil
    · subst t
      simp [extractMinAux, rootMerge, repairFirst, prepareLeft, descendFirst]
    cases merged : t.rootMerge with
    | some u =>
      obtain ⟨k, height, balanced, _⟩ := rootMerge_balance valid merged
      have drop := (rootMerge_spec merged).2.1
      have bound := ih balanced (by omega)
      simp only [extractMinAux, merged]
      omega
    | none =>
      have balanced := (repairFirst_ready valid merged).1
      have reserve := repairFirst_nodes t
      have positive : (t.repairFirst).1 ≠ .nil := by
        intro absent
        have sizes := (repairFirst_rotations t).size_eq
        rw [absent, binary, Tree.size, binary_size] at sizes
        cases t <;> simp only [size] at sizes <;> simp_all <;> omega
      have descent := descendFirst_cost (extractMinAux fuel) balanced positive
        (fun child k smaller childBalance => ih childBalance (by omega))
      have localCost := repairFirst_cost t
      simp only [extractMinAux, merged]
      omega

end RotationBST.Geometric.Split.Multiway
