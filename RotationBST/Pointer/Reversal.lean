module

public import RotationBST.Pointer.Traces

@[expose] public section

namespace RotationBST.Pointer

variable {a b : Config} {k : Nat}

/-- Undo one instruction. Reversing a rotation requires moving to the demoted
node, promoting it again, and restoring the old cursor. -/
theorem Step.reverse (h : Step a b) : ∃ j, j ≤ 3 ∧ Trace b a j := by
  cases h
  · exact ⟨1, by decide, .step .upLeft .refl⟩
  · exact ⟨1, by decide, .step .upRight .refl⟩
  · exact ⟨1, by decide, .step .downLeft .refl⟩
  · exact ⟨1, by decide, .step .downRight .refl⟩
  · exact ⟨3, by decide, .step .downRight (.step .rotateRightChild (.step .downLeft .refl))⟩
  · exact ⟨3, by decide, .step .downLeft (.step .rotateLeftChild (.step .downRight .refl))⟩

theorem Trace.reverse (h : Trace a b k) : ∃ j, j ≤ 3 * k ∧ Trace b a j := by
  induction h with
  | refl => exact ⟨0, by omega, .refl⟩
  | @step a b c k h _ ih =>
      obtain ⟨i, hi, ht⟩ := ih
      obtain ⟨j, hj, hr⟩ := h.reverse
      exact ⟨i + j, by omega, ht.append hr⟩

end RotationBST.Pointer
