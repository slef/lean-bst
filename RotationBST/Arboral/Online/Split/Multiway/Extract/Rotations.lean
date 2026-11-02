module

public import RotationBST.Arboral.Online.Split.Multiway.Extract.Abstract
public import RotationBST.Arboral.Online.Split.Multiway.Edges.Bounds

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway

theorem rootMerge_spec {t u : Multiway} (merged : t.rootMerge = some u) :
    t.binary = u.binary ∧ u.nodes + 2 = t.nodes ∧ u ≠ .nil := by
  cases t with
  | nil => simp [rootMerge] at merged
  | three a b c => simp [rootMerge] at merged
  | four a b c d => simp [rootMerge] at merged
  | two l r =>
    cases l <;> cases r <;> simp [rootMerge] at merged
    subst u
    exact ⟨rfl, merge_nodes _ _ _ _, by simp⟩

/-- The recursive minimum can be lifted through one multiway node in at most
two more rotations, without deleting or rearranging any other key. -/
theorem descendFirst_rotations (recur : Multiway → Multiway × Nat) (t : Multiway)
    (nonempty : t ≠ .nil)
    (recursive : ∀ child, child.nodes < t.nodes → child ≠ .nil →
      Rotations child.binary (.node .nil (recur child).1.binary) (recur child).2) :
    Rotations t.binary (.node .nil (descendFirst recur t).1.binary) (descendFirst recur t).2 := by
  cases t with
  | nil => contradiction
  | two l r =>
    by_cases empty : l = .nil
    · subst l; exact .refl
    · have step := recursive l (by simp only [nodes]; omega) empty
      simpa only [descendFirst, ite_eq_right empty, binary] using
        step.inLeft.append (.step .right .refl)
  | three l m r =>
    by_cases empty : l = .nil
    · subst l; exact .refl
    · have step := recursive l (by simp only [nodes]; omega) empty
      simpa only [descendFirst, ite_eq_right empty, binary] using
        step.inLeft.append (.step .right .refl)
  | four a b c d =>
    by_cases empty : a = .nil
    · subst a; exact .step .right .refl
    · have step := recursive a (by simp only [nodes]; omega) empty
      simpa only [descendFirst, ite_eq_right empty, binary] using
        step.inLeft.inLeft.append (.step (.inLeft .right) (.step .right .refl))


theorem extractMinAux_rotations (fuel : Nat) (t : Multiway) (enough : t.nodes < fuel)
    (nonempty : t ≠ .nil) :
    Rotations t.binary (.node .nil (extractMinAux fuel t).1.binary) (extractMinAux fuel t).2 := by
  induction fuel generalizing t with
  | zero => omega
  | succ fuel ih =>
    cases merged : t.rootMerge with
    | some u =>
      obtain ⟨same, drop, positive⟩ := rootMerge_spec merged
      have recursive := ih u (by omega) positive
      simpa only [extractMinAux, merged, same] using recursive
    | none =>
      have repair := repairFirst_rotations t
      have reserve := repairFirst_nodes t
      have positive : (t.repairFirst).1 ≠ .nil := by
        intro empty
        have sizes := repair.size_eq
        rw [empty, binary, Tree.size, binary_size] at sizes
        cases t <;> simp only [size] at sizes <;> simp_all <;> omega
      have descent := descendFirst_rotations (extractMinAux fuel) (t.repairFirst).1 positive
        (fun child smaller childNonempty => ih child (by omega) childNonempty)
      simpa only [extractMinAux, merged] using repair.append descent

/-- The extracted key is the original minimum, exposed at the binary root. -/
theorem extractMin_access (t : Multiway) (nonempty : t ≠ .nil) :
    Access t.binary (.node .nil (t.extractMin).1.binary) 0 (t.extractMin).2 :=
  ⟨extractMinAux_rotations _ t (by omega) nonempty, rfl⟩

/-- Extraction removes exactly one key. -/
theorem extractMin_size (t : Multiway) (nonempty : t ≠ .nil) :
    (t.extractMin).1.size + 1 = t.size := by
  have equal := (extractMin_access t nonempty).1.size_eq
  simp only [Tree.size, binary_size] at equal
  omega

end RotationBST.Arboral.Split.Multiway
