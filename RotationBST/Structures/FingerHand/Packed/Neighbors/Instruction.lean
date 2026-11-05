module

public import RotationBST.Structures.FingerHand.Packed.Neighbors.State
public import RotationBST.Models.Pointer.Location
public import RotationBST.Models.Multifinger.Proofs

@[expose] public section
namespace RotationBST.FingerHand.Hand

private theorem key_at_root (t : Tree) (cs : List Pointer.Frame) (nonempty : t ≠ .nil) :
    (Pointer.Config.mk t cs).key? = some (Pointer.offset cs + rootRank t) := by
  cases t with
  | nil => exact False.elim (nonempty rfl)
  | node => rfl

/-- Make the destination key of an actual multifinger instruction available in
the current reference tree. For a rotation the key is unchanged; this prepares
the destination only and does not yet perform the reference rotation. -/
theorem expose_instruction {fingers : Nat} {h : Hand} {s t : Multifinger.State fingers}
    {i : Fin fingers} (rep : h.Represents s) (valid : s.Valid) (step : Multifinger.Step s i t) :
    ∃ (after : Hand) (k : Nat), Exposure h after (t.position i) ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 180 + 20 * (fingers + 1) + h.potential := by
  cases step with
  | @execute a b x tree key instruction touched =>
    simp only [Function.update_self]
    obtain ⟨fs, cs, d, l, r, shape, referenceTree, referenceKey, depth⟩ := rep.locate valid i
    have cursor : a = ⟨.node l.reference r.reference, cs ++ Context.referencePath fs⟩ :=
      Pointer.Config.ext_key (tree.trans referenceTree.symm) key referenceKey
    rw [cursor] at instruction
    rw [shape] at rep ⊢
    rcases instruction.destination with same | ⟨nonempty, rfl⟩ | ⟨nonempty, rfl⟩ | ⟨f, ds, path, rfl⟩
    · have eq : x = s.position i := Option.some.inj (touched.symm.trans (same.trans referenceKey))
      refine ⟨_, 0, ⟨rep.1, rfl, fun _ => .refl _, by omega, ?_⟩, .refl, by omega⟩
      rw [eq]
      exact rep.finger valid i
    · have index := Option.some.inj ((key_at_root _ _ nonempty).symm.trans touched)
      simp only [Pointer.offset, Pointer.offset_append] at index
      obtain ⟨after, k, ex, trace, cost⟩ := expose_left fs cs d l r rep.1 nonempty
      have bound := state_cost fs (.node cs d l r) rep cost
      have eq : x = Pointer.offset (Context.referencePath fs) + Pointer.offset cs + rootRank l.reference := by omega
      exact ⟨after, k, eq.symm ▸ ex, trace, by omega⟩
    · have index := Option.some.inj ((key_at_root _ _ nonempty).symm.trans touched)
      simp only [Pointer.offset, Pointer.offset_append] at index
      obtain ⟨after, k, ex, trace, cost⟩ := expose_right fs cs d l r rep.1 nonempty
      have bound := state_cost fs (.node cs d l r) rep cost
      have eq : x = Pointer.offset (Context.referencePath fs) + Pointer.offset cs +
          l.reference.size + 1 + rootRank r.reference := by omega
      exact ⟨after, k, eq.symm ▸ ex, trace, by omega⟩
    · have nonempty : Pointer.plug [f] (.node l.reference r.reference) ≠ .nil := by cases f <;> simp [Pointer.plug]
      have index := Option.some.inj ((key_at_root _ _ nonempty).symm.trans touched)
      obtain ⟨after, k, ex, trace, cost⟩ := expose_parent fs cs d l r rep.1 f ds path
      exact ⟨after, k, index ▸ ex, trace, state_cost fs (.node cs d l r) rep cost⟩

end RotationBST.FingerHand.Hand
