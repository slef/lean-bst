module

public import RotationBST.Models.Pointer.Simulation
public import RotationBST.Models.Rotation.Existence.Proofs
public import RotationBST.Bounds.Normalization.Proofs
public import Mathlib.Tactic.Linarith
public import RotationBST.Models.Pointer.Lazy.Online.Correctness

@[expose] public section

namespace RotationBST.Pointer.Lazy.Online

theorem from_initial (a : Algorithm) (past : List Nat) (t : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < t.size) :
    Pointer.Execution t xs (run a past (initial t) xs).1.current (run a past (initial t) xs).2 ∧
    Rotations (run a past (initial t) xs).1.current (a.runFrom past t xs).1
      (run a past (initial t) xs).1.pending ∧
    (run a past (initial t) xs).2 + 32 * (run a past (initial t) xs).1.pending ≤
      32 * (a.runFrom past t xs).2 + 17 * xs.length := by
  obtain ⟨heq, hexec, hcost⟩ := run_spec a past (initial t) xs valid
  have hr := (run a past (initial t) xs).1.certificate
  rw [heq] at hr
  exact ⟨hexec, hr, by simpa only [initial, Nat.zero_add] using hcost⟩

/-- Every working-set algorithm in the shape model induces a causal pointer
strategy with the same asymptotic working-set guarantee. -/
theorem workingSet_transfer (a : Algorithm) (workingSet : HasWorkingSetBound a) :
    ∃ C D : Nat, ∀ t xs, (∀ x ∈ xs, x < t.size) →
      (run a [] (initial t) xs).2 ≤ C * workingSetSum t.size [] xs +
        D * t.size * (1 + t.size.log2) := by
  obtain ⟨C, D, hc⟩ := workingSet
  refine ⟨32 * C + 17, 32 * D, ?_⟩
  intro t xs valid
  have hs := (from_initial a [] t xs valid).2.2
  have hb := hc t xs valid
  have hl := BoundsBridge.length_le_workingSetSum t.size [] xs
  unfold Algorithm.cost at hb
  nlinarith

/-- Conditional transfer of dynamic optimality to the pointer model. This does
not assert dynamic optimality of splay or of any other particular algorithm. -/
theorem dynamic_transfer (a : Algorithm) (optimal : TotallyDynamicallyOptimal a) :
    ∃ C D : Nat, ∀ t xs u k, Pointer.Execution t xs u k →
      (run a [] (initial t) xs).2 ≤ C * k + D * t.size := by
  obtain ⟨C, D, hc⟩ := optimal
  refine ⟨96 * C, 32 * D, ?_⟩
  intro t xs u k execution
  obtain ⟨v, r, q, hr, _, hk⟩ := Pointer.execution_to_rotations execution
  have valid := AccessBridge.execution_valid hr
  have hs := (from_initial a [] t xs valid).2.2
  have hb := hc t xs v r hr
  have hm := Nat.mul_le_mul_left C (show xs.length + r ≤ 3 * k by omega)
  unfold Algorithm.totalCost Algorithm.cost at hb
  nlinarith

end RotationBST.Pointer.Lazy.Online
