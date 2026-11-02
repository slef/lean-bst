module

public import RotationBST.Arboral.Online.Split.Finger.Binary.Bounds

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

private theorem binaryView_first (t : Multiway) :
    binaryView t = ⟨[], .nil⟩ ∨ ∃ rest tail, binaryView t = ⟨.nil :: rest, tail⟩ := by
  induction t with
  | nil => exact Or.inl rfl
  | two a b ia ib =>
    apply Or.inr
    rcases ia with empty | ⟨rest, tail, equal⟩
    · exact ⟨[], b.binary, by simp [binaryView, empty]⟩
    · exact ⟨rest ++ [tail], b.binary, by simp [binaryView, equal]⟩
  | three a b c ia ib ic =>
    apply Or.inr
    rcases ia with empty | ⟨rest, tail, equal⟩
    · exact ⟨[b.binary], c.binary, by simp [binaryView, empty]⟩
    · exact ⟨rest ++ [tail, b.binary], c.binary, by simp [binaryView, equal]⟩
  | four a b c d ia ib ic id =>
    apply Or.inr
    rcases ia with empty | ⟨rest, tail, equal⟩
    · exact ⟨[b.binary, c.binary], d.binary, by simp [binaryView, empty]⟩
    · exact ⟨rest ++ [tail, b.binary, c.binary], d.binary, by simp [binaryView, equal]⟩

/-- The concrete minimum finger really has the minimum key at the binary root. -/
theorem binaryView_minimum (t : Multiway) (nonempty : t ≠ .nil) :
    Access t.binary (binaryView t).tree 0 (viewCost t) := by
  refine ⟨binaryView_rotations t, ?_⟩
  rcases binaryView_first t with empty | ⟨rest, tail, equal⟩
  · have sizes := binaryView_size t
    rw [empty] at sizes
    cases t <;> simp only [BinaryView.tree, comb, Tree.size, size] at sizes <;> simp_all
  · simp only [equal, BinaryView.tree, comb, Tree.size]

end RotationBST.Arboral.Split.Multiway.Finger
