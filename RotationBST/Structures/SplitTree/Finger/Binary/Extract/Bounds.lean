module

public import RotationBST.Structures.SplitTree.Finger.Binary.Extract.Rotations

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger

private theorem descent_cost (cost : Multiway → Nat) {h : Nat} {t : Multiway}
    (valid : Balanced h t) (nonempty : t ≠ .nil)
    (recursive : ∀ child k, child.nodes < t.nodes → Balanced k child → cost child ≤ 3 * k) :
    (if firstChild t = .nil then 0 else cost (firstChild t)) + 3 ≤ 3 * h := by
  cases valid with
  | nil => contradiction
  | @two k l r ha hb =>
    have bound := recursive l k (by simp only [nodes]; omega) ha
    by_cases empty : l = .nil <;> simp only [firstChild, empty, ite_true, ite_false] <;> omega
  | @three k l m r ha hb hc =>
    have bound := recursive l k (by simp only [nodes]; omega) ha
    by_cases empty : l = .nil <;> simp only [firstChild, empty, ite_true, ite_false] <;> omega
  | @four k a b c d ha hb hc hd =>
    have bound := recursive a k (by simp only [nodes]; omega) ha
    by_cases empty : a = .nil <;> simp only [firstChild, empty, ite_true, ite_false] <;> omega

/-- Maintaining the finger encoding during minimum extraction costs at most
three rotations per multiway level, including inside a larger interval. -/
theorem extractFingerAux_cost (fuel : Nat) {h : Nat} {t : Multiway}
    (valid : Balanced h t) (enough : t.nodes < fuel) :
    extractOpenCost fuel t ≤ 3 * h ∧ extractViewCost fuel t ≤ 3 * h := by
  induction fuel generalizing h t with
  | zero => omega
  | succ fuel ih =>
    by_cases empty : t = .nil
    · subst t
      simp [extractOpenCost, extractViewCost, rootMerge, repairFirst, prepareLeft,
        firstChild, repairOpenCost, repairViewCost]
    cases merged : t.rootMerge with
    | some u =>
      obtain ⟨k, height, balanced, _⟩ := rootMerge_balance valid merged
      have drop := (rootMerge_spec merged).2.1
      have bound := ih balanced (by omega)
      simp only [extractOpenCost, extractViewCost, merged]
      constructor <;> omega
    | none =>
      have balanced := (repairFirst_ready valid merged).1
      have reserve := repairFirst_nodes t
      have positive : (t.repairFirst).1 ≠ .nil := by
        intro absent
        have sizes := (repairFirst_rotations t).size_eq
        rw [absent, binary, Tree.size, binary_size] at sizes
        cases t <;> simp only [size] at sizes <;> simp_all
      have descent := descent_cost (extractOpenCost fuel) balanced positive
        (fun child k smaller childBalance => (ih childBalance (by omega)).1)
      have openBound := repairOpenCost_bound t
      have viewBound := repairViewCost_bound t
      simp only [extractOpenCost, extractViewCost, merged]
      constructor <;> omega

end RotationBST.SplitTree.Multiway.Finger
