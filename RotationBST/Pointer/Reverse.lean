module

public import RotationBST.Pointer.Simulation
public import RotationBST.Pointer.Traces

@[expose] public section

namespace RotationBST.Pointer

variable {s t : Tree} {xs : List Nat} {x k : Nat}

/-- A shape rotation has nonempty source and target. -/
theorem rotate_nonempty (h : Rotate s t) : s ≠ .nil ∧ t ≠ .nil := by
  cases h <;> constructor <;> intro h <;> cases h

/-- Eager simulation preserves the exact endpoint. Its overhead depends on tree
size: this is not the constant-factor lazy-simulation theorem. -/
theorem rotate_trace (h : Rotate s t) :
    ∃ k, k ≤ 2 * s.size ∧ Trace ⟨s, []⟩ ⟨t, []⟩ k := by
  induction h with
  | right => exact ⟨2, by simp [Tree.size]; omega,
      .step .downLeft (.step .rotateLeftChild .refl)⟩
  | left => exact ⟨2, by simp [Tree.size]; omega,
      .step .downRight (.step .rotateRightChild .refl)⟩
  | @inLeft a b c h ih =>
      obtain ⟨k, hk, ht⟩ := ih
      obtain ⟨ha, hb⟩ := rotate_nonempty h
      cases a with
      | nil => exact False.elim (ha rfl)
      | node a₁ a₂ =>
          cases b with
          | nil => exact False.elim (hb rfl)
          | node b₁ b₂ =>
              have ht' := ht.under [.left c]
              refine ⟨1 + k + 1, ?_, ?_⟩
              · simp only [Tree.size] at *; omega
              · simpa only [Nat.add_comm 1 k] using
                  (Trace.step Step.downLeft ht').append (Trace.step Step.upLeft .refl)
  | @inRight a b c h ih =>
      obtain ⟨k, hk, ht⟩ := ih
      obtain ⟨ha, hb⟩ := rotate_nonempty h
      cases a with
      | nil => exact False.elim (ha rfl)
      | node a₁ a₂ =>
          cases b with
          | nil => exact False.elim (hb rfl)
          | node b₁ b₂ =>
              have ht' := ht.under [.right c]
              refine ⟨1 + k + 1, ?_, ?_⟩
              · simp only [Tree.size] at *; omega
              · simpa only [Nat.add_comm 1 k] using
                  (Trace.step Step.downRight ht').append (Trace.step Step.upRight .refl)

/-- Simulate a complete rotation trace, returning the pointer to the root after
 each rotation. The tree-size factor is explicit. -/
theorem rotations_trace (h : Rotations s t k) :
    ∃ m, m ≤ 2 * s.size * k ∧ Trace ⟨s, []⟩ ⟨t, []⟩ m := by
  induction h with
  | refl => exact ⟨0, by simp, .refl⟩
  | step h _ ih =>
      obtain ⟨a, ha, ht⟩ := rotate_trace h
      obtain ⟨b, hb, hu⟩ := ih
      rw [← h.size_eq] at hb
      refine ⟨a + b, ?_, ht.append hu⟩
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- Exact endpoint simulation of one root access, with size-dependent overhead. -/
theorem access_to_pointer (h : Access s t x k) :
    ∃ m, m ≤ 1 + 2 * s.size * k ∧ Serves s t x m := by
  obtain ⟨m, hm, ht⟩ := rotations_trace h.1
  refine ⟨1 + m, by omega, ⟨⟨t, []⟩, ⟨t, []⟩, m, 0, ht, ?_, .refl, rfl, by omega⟩⟩
  cases t with
  | nil => exact False.elim h.2
  | node l r => simpa only [Config.key?, offset, Nat.zero_add] using congrArg some h.2

/-- Every rotation-only execution has a pointer execution with the exact same
final tree. This bound does not assert asymptotic equivalence of the models. -/
theorem execution_to_pointer (h : RotationBST.Execution s xs t k) :
    ∃ m, m ≤ xs.length + 2 * s.size * k ∧ Execution s xs t m := by
  induction h with
  | nil => exact ⟨0, by simp, .nil⟩
  | cons ha _ ih =>
      obtain ⟨a, hka, hpa⟩ := access_to_pointer ha
      obtain ⟨b, hkb, hpb⟩ := ih
      rw [← ha.1.size_eq] at hkb
      refine ⟨a + b, ?_, .cons hpa hpb⟩
      simp only [List.length_cons, Nat.mul_add]
      omega

end RotationBST.Pointer
