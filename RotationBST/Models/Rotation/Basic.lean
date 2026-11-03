module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section

namespace RotationBST

variable {s t : Tree} {x k : Nat} {xs : List Nat}

theorem Rotate.size_eq (h : Rotate s t) : s.size = t.size := by
  induction h with
  | right => simp only [Tree.size]; omega
  | left => simp only [Tree.size]; omega
  | inLeft _ ih => simp only [Tree.size, ih]
  | inRight _ ih => simp only [Tree.size, ih]

theorem Rotations.size_eq (h : Rotations s t k) : s.size = t.size := by
  induction h with
  | refl => rfl
  | step h _ ih => exact h.size_eq.trans ih

theorem Access.in_range (h : Access s t x k) : x < s.size := by
  obtain ⟨hr, hx⟩ := h
  rw [hr.size_eq]
  cases t with
  | nil => exact hx.elim
  | node l r => simp only [Tree.size]; change l.size = x at hx; omega

theorem Execution.size_eq (h : Execution s xs t k) : s.size = t.size := by
  induction h with
  | nil => rfl
  | cons ha _ ih => exact ha.1.size_eq.trans ih

end RotationBST
