module

public import RotationBST.Arboral.Online.Split.Finger.Binary.Extract.Descent
public import RotationBST.Arboral.Online.Split.Multiway.Extract.Balance

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Finger-maintaining extraction works both at the root and inside an interval
with an arbitrary larger-key remainder. -/
theorem extractFingerAux_rotations (fuel : Nat) {h : Nat} {t : Multiway}
    (valid : Balanced h t) (enough : t.nodes < fuel) (nonempty : t ≠ .nil) :
    (∀ rest, Rotations (openView t rest) (.node .nil (openView (extractMinAux fuel t).1 rest))
        (extractOpenCost fuel t)) ∧
      Rotations (binaryView t).tree (.node .nil (binaryView (extractMinAux fuel t).1).tree)
        (extractViewCost fuel t) := by
  induction fuel generalizing h t with
  | zero => omega
  | succ fuel ih =>
    cases merged : t.rootMerge with
    | some u =>
      obtain ⟨_, _, balance, _⟩ := rootMerge_balance valid merged
      obtain ⟨_, drop, positive⟩ := rootMerge_spec merged
      obtain ⟨inside, root⟩ := ih balance (by omega) positive
      obtain ⟨same, repair⟩ := rootMerge_view merged
      constructor
      · intro rest
        simpa only [extractMinAux, extractOpenCost, merged] using (repair rest).append (inside rest)
      · simpa only [extractMinAux, extractViewCost, merged, same] using root
    | none =>
      have balance := (repairFirst_ready valid merged).1
      have reserve := repairFirst_nodes t
      have positive : (t.repairFirst).1 ≠ .nil := by
        intro absent
        have sizes := (repairFirst_rotations t).size_eq
        rw [absent, binary, Tree.size, binary_size] at sizes
        cases t <;> simp only [size] at sizes <;> simp_all
      have recursive := fun child k (smaller : child.nodes < (t.repairFirst).1.nodes)
        (childBalance : Balanced k child) (childNonempty : child ≠ .nil) =>
          (ih childBalance (by omega) childNonempty).1
      constructor
      · intro rest
        have step := (repairOpen_rotations t rest).append
          (descendFirst_open (extractMinAux fuel) (extractOpenCost fuel) balance positive recursive rest)
        simpa only [extractMinAux, extractOpenCost, merged] using step
      · simp only [extractMinAux, extractViewCost, merged]
        have step := (repairView_rotations t).append
          (descendFirst_view (extractMinAux fuel) (extractOpenCost fuel) balance positive recursive)
        exact step

/-- Minimum extraction returns precisely the finger encoding of its balanced
multiway result, so later operations can keep using the same representation. -/
theorem extractView_access {h : Nat} {t : Multiway} (valid : Balanced h t) (nonempty : t ≠ .nil) :
    Access (binaryView t).tree (.node .nil (binaryView (extractView t).1).tree) 0 (extractView t).2 :=
  ⟨(extractFingerAux_rotations _ valid (by omega) nonempty).2, rfl⟩

end RotationBST.Arboral.Split.Multiway.Finger
