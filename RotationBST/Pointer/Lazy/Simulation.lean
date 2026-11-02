module

public import RotationBST.Pointer.Lazy.Projection
public import RotationBST.Model.Basic

@[expose] public section

namespace RotationBST.Pointer.Lazy

variable {s t : Tree} {x k : Nat}

/-- Serve a root access using linear pointer work in its selected rotation
component. Other rotations remain as a suffix, and retain their exact cost. -/
theorem access_to_pointer (h : Access s t x k) :
    ∃ q r d c, Pointer.Serves s q x c ∧ Rotations q t d ∧
      r + d = k ∧ c ≤ 32 * r + 17 := by
  cases s with
  | nil => have := h.in_range; simp [Tree.size] at this
  | node l r =>
      let s := Tree.node l r
      have hl := (Representation.Bridge.access_iff s t x k).mp h
      obtain ⟨ops, hlen, ht⟩ := trace_of_rotations hl.1
      have hd : (s.labelFrom 0).inorder.Nodup := by
        rw [Representation.Bridge.inorder_label]
        exact List.nodup_range'
      have hroot : rootKey? (t.labelFrom 0) = some x := by
        cases t with
        | nil => exact False.elim h.2
        | node a b => simpa only [Tree.labelFrom, rootKey?, Nat.zero_add] using congrArg some h.2
      obtain ⟨color, q, hu, _, hc, hn, hs, ha, hp, hcount⟩ :=
        rooted_normal_form ht hd (r := l.size) (by simp [s, Tree.labelFrom, rootKey?]) hroot
      have selected : ∀ e ∈ ops.filter (fun e => color e.1),
          color e.1 = true ∧ color e.2 = true := by
        intro e he
        obtain ⟨he, hec⟩ := List.mem_filter.mp he
        exact ⟨hec, (hu e he).symm.trans hec⟩
      have hf := hs.project_fringe color selected hd hc
      obtain ⟨p, hpc, hpt⟩ := Skeleton.reshape (project color (s.labelFrom 0)) (project color q) hf
      rw [project_tree, project_tree, Representation.Bridge.erase_label] at hpt
      rw [project_size] at hpc
      have hsize : s.size = q.erase.size := by
        simpa only [Representation.Bridge.erase_label] using
          (Representation.Bridge.erase_rotations hs.forget).size_eq
      have hcanon : q.erase.labelFrom 0 = q := Representation.Bridge.reconstruct q 0 (by
        rw [← Representation.Bridge.inorder_rotations hs.forget,
          Representation.Bridge.inorder_label, hsize])
      have haccess : Access s q.erase x (ops.filter fun e => color e.1).length := by
        apply (Representation.Bridge.access_iff _ _ _ _).mpr
        rw [hcanon]
        exact ha
      have hserve : Pointer.Serves s q.erase x (1 + p) := by
        refine ⟨⟨q.erase, []⟩, ⟨q.erase, []⟩, p, 0, hpt, ?_, .refl, rfl, by omega⟩
        cases he : q.erase with
        | nil => rw [he] at haccess; exact False.elim haccess.2
        | node a b =>
            rw [he] at haccess
            simpa only [Pointer.Config.key?, Pointer.offset, Nat.zero_add] using congrArg some haccess.2
      refine ⟨q.erase, (ops.filter fun e => color e.1).length,
        (ops.filter fun e => !(color e.1)).length, 1 + p, hserve, ?_, ?_, ?_⟩
      · simpa only [Representation.Bridge.erase_label] using Representation.Bridge.erase_rotations hp.forget
      · omega
      · omega

/-- Pending rotations are charged once, when their component next participates
in an access. The final pending suffix remains explicitly in the cost bound. -/
theorem execution_pending {s t u : Tree} {xs : List Nat} {i k : Nat}
    (h : RotationBST.Execution t xs u k) (pending : Rotations s t i) :
    ∃ v c d, Pointer.Execution s xs v c ∧ Rotations v u d ∧
      c + 32 * d ≤ 32 * (i + k) + 17 * xs.length := by
  induction h generalizing s i with
  | nil => exact ⟨s, 0, i, .nil, pending, by simp⟩
  | @cons t v x a xs u b ha _ ih =>
      have haccess : Access s v x (i + a) := ⟨pending.append ha.1, ha.2⟩
      obtain ⟨q, r, d, c, hserve, hrest, hcount, hcost⟩ := access_to_pointer haccess
      obtain ⟨w, e, f, hexec, hfinal, hbound⟩ := ih hrest
      refine ⟨w, c + e, f, .cons hserve hexec, hfinal, ?_⟩
      simp only [List.length_cons]
      omega

/-- Every root-access rotation execution has a constant-factor pointer
simulation. It may defer a final rotation suffix, whose cost is also bounded. -/
theorem execution_to_pointer {s t : Tree} {xs : List Nat} {k : Nat}
    (h : RotationBST.Execution s xs t k) :
    ∃ u c d, Pointer.Execution s xs u c ∧ Rotations u t d ∧
      c + 32 * d ≤ 32 * k + 17 * xs.length := by
  simpa only [Nat.zero_add] using execution_pending h (Rotations.refl (t := s))

end RotationBST.Pointer.Lazy
