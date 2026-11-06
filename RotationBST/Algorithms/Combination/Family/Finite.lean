module

public import RotationBST.Algorithms.Combination.Family.Balanced
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Family

/-- Pad any fixed finite family to a balanced tree. Repeated leaves do not
change the comparator: one output retains all original guarantees. -/
theorem finite {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (depth overhead C₀ C₁ : Nat) (capacity : Fintype.card ι ≤ 2 ^ depth)
    (inputs : ι → Algorithm saved) (charges : ι → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ depth * overhead) C₀ (C₁ + depth)
        (chargeScale C₀ C₁ depth) charges := by
  classical
  have enough : Fintype.card ι ≤ Fintype.card (Index depth) := by simpa [Index] using capacity
  obtain ⟨embedding⟩ := Function.Embedding.nonempty_of_card_le enough
  let cover : Index depth → ι := Function.invFun embedding
  obtain ⟨output, guaranteed⟩ := balanced depth overhead C₀ C₁
    (fun i => inputs (cover i)) (fun i => charges (cover i)) (fun i => well (cover i))
    nonempty size fields oldData
  refine ⟨output, ?_⟩
  intro i
  obtain ⟨j, rfl⟩ := Function.invFun_surjective embedding.injective i
  exact guaranteed j

/-- Every nonempty finite family admits a fixed online combination using
the least depth whose balanced tree contains enough leaves. -/
theorem exists_combination {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (overhead C₀ C₁ : Nat) (inputs : ι → Algorithm saved) (charges : ι → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ (Nat.clog 2 (Fintype.card ι)) * overhead) C₀ (C₁ + Nat.clog 2 (Fintype.card ι))
        (chargeScale C₀ C₁ (Nat.clog 2 (Fintype.card ι))) charges :=
  finite _ overhead C₀ C₁ (Nat.le_pow_clog (by decide) _) inputs charges well nonempty size fields oldData

end RotationBST.Combo.Family
