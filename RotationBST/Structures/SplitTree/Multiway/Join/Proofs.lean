module

public import RotationBST.Structures.SplitTree.Multiway.Join.Left

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Join

theorem finish_tree (h : Nat) (result : Promotion × Nat) :
    (finish h result).tree = result.1.tree := by
  obtain ⟨up, cost⟩ := result
  cases up <;> rfl

theorem finish_cost (h : Nat) (result : Promotion × Nat) :
    (finish h result).cost = result.2 := by
  obtain ⟨up, cost⟩ := result
  cases up <;> rfl

theorem finish_balance {h : Nat} {result : Promotion × Nat} (valid : result.1.Valid h) :
    Balanced (finish h result).height (finish h result).tree ∧
      h ≤ (finish h result).height ∧ (finish h result).height ≤ h + 1 := by
  obtain ⟨up, cost⟩ := result
  cases up with
  | stay t => exact ⟨valid, Nat.le_refl _, by simp [finish]⟩
  | rise l r => exact ⟨.two valid.1 valid.2, by simp [finish], Nat.le_refl _⟩

theorem run_rotations (hl hr : Nat) (l r : Multiway) :
    Rotations (.node l.binary r.binary) (run hl hr l r).tree.binary (run hl hr l r).cost := by
  unfold run
  split <;> simp only [finish_tree, finish_cost]
  · exact joinRight_rotations _ _ _
  · exact joinLeft_rotations _ _ _

theorem run_cost (hl hr : Nat) (l r : Multiway) :
    (run hl hr l r).cost ≤ 3 * (hl - hr + (hr - hl)) := by
  unfold run
  split <;> simp only [finish_cost]
  · have bound := joinRight_cost (hl - hr) l r
    omega
  · have bound := joinLeft_cost (hr - hl) l r
    omega

theorem run_balance {hl hr : Nat} {l r : Multiway} (left : Balanced hl l) (right : Balanced hr r) :
    Balanced (run hl hr l r).height (run hl hr l r).tree ∧
      max hl hr ≤ (run hl hr l r).height ∧ (run hl hr l r).height ≤ max hl hr + 1 := by
  unfold run
  split
  · have taller : Balanced (hr + (hl - hr)) l := by
      rw [show hr + (hl - hr) = hl by omega]; exact left
    have result := finish_balance (joinRight_balance (hl - hr) taller right)
    have eq : hr + (hl - hr) = hl := by omega
    rw [eq] at result
    rw [Nat.max_eq_left (show hr ≤ hl by assumption)]
    exact result
  · have taller : Balanced (hl + (hr - hl)) r := by
      rw [show hl + (hr - hl) = hr by omega]; exact right
    have result := finish_balance (joinLeft_balance (hr - hl) left taller)
    have eq : hl + (hr - hl) = hr := by omega
    rw [eq] at result
    rw [Nat.max_eq_right (show hl ≤ hr by omega)]
    exact result

theorem run_size (hl hr : Nat) (l r : Multiway) :
    (run hl hr l r).tree.size = l.size + 1 + r.size := by
  have sizes := (run_rotations hl hr l r).size_eq
  simpa only [Tree.size, binary_size] using sizes.symm

end RotationBST.SplitTree.Multiway.Join
