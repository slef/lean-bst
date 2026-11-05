module

public import RotationBST.Models.Pointer.Search

@[expose] public section
namespace RotationBST.Pointer

/-- Append two conventional request executions, preserving their actual costs. -/
theorem Execution.append {s t u : Tree} {xs ys : List Nat} {k m : Nat}
    (first : Execution s xs t k) (last : Execution t ys u m) :
    Execution s (xs ++ ys) u (k + m) := by
  induction first with
  | nil => simpa using last
  | cons request _ ih => simpa only [List.cons_append, Nat.add_assoc] using Execution.cons request (ih last)

/-- A static root search traverses the search path out and back and charges one
unit for the request. The resulting tree is unchanged. -/
theorem static_request (t : Tree) (x : Nat) (valid : x < t.size) :
    Serves t t x (1 + 2 * Tree.depth t x) := by
  obtain ⟨cursor, _, key, outward, inward⟩ := search_walk t x valid
  exact ⟨cursor, ⟨t, []⟩, Tree.depth t x, Tree.depth t x,
    outward, key, inward, rfl, by omega⟩

/-- Uniformly shallow requests have a legal, uniformly cheap conventional
execution in a fixed tree. The physical tree is unchanged throughout. -/
theorem shallow_execution (t : Tree) (xs : List Nat) (depth : Nat)
    (valid : ∀ x ∈ xs, x < t.size) (shallow : ∀ x ∈ xs, Tree.depth t x ≤ depth) :
    ∃ k, Execution t xs t k ∧ k ≤ (1 + 2 * depth) * xs.length := by
  induction xs with
  | nil => exact ⟨0, .nil, by simp⟩
  | cons x xs ih =>
    obtain ⟨k, rest, bound⟩ := ih (by intro y hy; exact valid y (by simp [hy]))
      (by intro y hy; exact shallow y (by simp [hy]))
    refine ⟨(1 + 2 * Tree.depth t x) + k,
      .cons (static_request t x (valid x (by simp))) rest, ?_⟩
    have first := shallow x (by simp)
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

end RotationBST.Pointer
