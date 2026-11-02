module

public import RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

private theorem maximumView_first (t : Multiway) :
    maximumView t = ⟨[], .nil⟩ ∨ ∃ rest tail, maximumView t = ⟨.nil :: rest, tail⟩ := by
  induction t with
  | nil => exact Or.inl rfl
  | two a b ia ib =>
    apply Or.inr
    rcases ib with empty | ⟨rest, tail, equal⟩
    · exact ⟨[], a.binary, by simp [maximumView, empty]⟩
    · exact ⟨rest ++ [tail], a.binary, by simp [maximumView, equal]⟩
  | three a b c ia ib ic =>
    apply Or.inr
    rcases ic with empty | ⟨rest, tail, equal⟩
    · exact ⟨[b.binary], a.binary, by simp [maximumView, empty]⟩
    · exact ⟨rest ++ [tail, b.binary], a.binary, by simp [maximumView, equal]⟩
  | four a b c d ia ib ic id =>
    apply Or.inr
    rcases id with empty | ⟨rest, tail, equal⟩
    · exact ⟨[c.binary, b.binary], a.binary, by simp [maximumView, empty]⟩
    · exact ⟨rest ++ [tail, c.binary, b.binary], a.binary, by simp [maximumView, equal]⟩

theorem maximumView_maximum (t : Multiway) (nonempty : t ≠ .nil) :
    Access t.binary (maximumView t).tree (t.size - 1) (maximumCost t) := by
  refine ⟨maximum_rotations t, ?_⟩
  have sizes := maximumView_size t
  rcases maximumView_first t with empty | ⟨rest, tail, equal⟩
  · rw [empty] at sizes
    cases t <;> simp only [MaximumView.tree, leftComb, Tree.size, size] at sizes <;> simp_all
  · rw [equal] at sizes ⊢
    simp only [MaximumView.tree, leftComb, Tree.size] at sizes ⊢
    omega

end RotationBST.Arboral.Split.Multiway.Finger
