module

public import RotationBST.Structures.FingerHand.Pruning.Basic
public import Mathlib.Data.List.Nodup

@[expose] public section
namespace RotationBST.FingerHand

theorem Contracts.sublist {s t : LabelledTree Nat} (h : Contracts s t) :
    t.inorder.Sublist s.inorder := by
  induction h with
  | empty => exact List.nil_sublist _
  | node x _ _ il ir => exact il.append (List.Sublist.cons_cons x ir)
  | left x _ ih => exact ih.trans (List.sublist_append_left _ _)
  | right x _ ih => exact (ih.cons x).trans (List.sublist_append_right _ _)

theorem Contracts.size_le {s t : LabelledTree Nat} (h : Contracts s t) :
    t.erase.size ≤ s.erase.size := by
  simpa only [Representation.Bridge.inorder_length] using h.sublist.length_le

theorem Contracts.eq_of_size {s t : LabelledTree Nat} (h : Contracts s t)
    (size : s.erase.size = t.erase.size) : s = t := by
  induction h with
  | empty t => cases t <;> simp_all [LabelledTree.erase, Tree.size]
  | node x hl hr il ir =>
    have := hl.size_le
    have := hr.size_le
    simp only [LabelledTree.erase, Tree.size] at size
    rw [il (by omega), ir (by omega)]
  | left x hl ih =>
    have := hl.size_le
    simp only [LabelledTree.erase, Tree.size] at size
    omega
  | right x hr ih =>
    have := hr.size_le
    simp only [LabelledTree.erase, Tree.size] at size
    omega

theorem prune_contracts (marks : Finset Nat) (t : LabelledTree Nat) : Contracts t (prune marks t) := by
  induction t with
  | nil => exact .empty _
  | node l x r il ir =>
    by_cases hx : x ∈ marks
    · simpa only [prune, join, hx, ↓reduceIte] using Contracts.node x il ir
    · cases hl : prune marks l <;> cases hr : prune marks r <;>
        simp only [prune, join, hx, ↓reduceIte, hl, hr] at *
      · exact .empty _
      · exact .right x ir
      · exact .left x il
      · exact .node x il ir

theorem node_distinct {l r : LabelledTree Nat} {x : Nat}
    (h : (LabelledTree.node l x r).inorder.Nodup) :
    l.inorder.Nodup ∧ r.inorder.Nodup ∧ x ∉ l.inorder ∧ x ∉ r.inorder ∧
      ∀ y ∈ l.inorder, y ∉ r.inorder := by
  simp only [LabelledTree.inorder, List.nodup_append', List.nodup_cons] at h
  have dis := List.disjoint_left.mp h.2.2
  exact ⟨h.1, h.2.1.2, fun hx => dis hx (List.mem_cons_self ..), h.2.1.1,
    fun y hy hr => dis hy (List.mem_cons_of_mem _ hr)⟩

/-- Any contraction retaining all requested marks is sufficient to recompute
their exact skeleton. Distinct labels prevent a different occurrence of the
same label from falsely witnessing retention. -/
theorem Contracts.project {s t : LabelledTree Nat} (h : Contracts s t) (marks : Finset Nat)
    (distinct : s.inorder.Nodup)
    (covers : ∀ x ∈ s.inorder, x ∈ marks → x ∈ t.inorder) :
    prune marks t = prune marks s := by
  induction h with
  | empty s =>
    symm
    apply (prune_nil_iff marks s).mpr
    intro x hx hm
    have := covers x hx hm
    simp [LabelledTree.inorder] at this
  | @node l r a b x hl hr il ir =>
    obtain ⟨dl, dr, xl, xr, apart⟩ := node_distinct distinct
    have left : ∀ y ∈ l.inorder, y ∈ marks → y ∈ a.inorder := by
      intro y hy hm
      have found := covers y (List.mem_append_left _ hy) hm
      simp only [LabelledTree.inorder, List.mem_append, List.mem_cons] at found
      rcases found with found | eq | found
      · exact found
      · exact False.elim (xl (eq ▸ hy))
      · exact False.elim (apart y hy (hr.sublist.subset found))
    have right : ∀ y ∈ r.inorder, y ∈ marks → y ∈ b.inorder := by
      intro y hy hm
      have found := covers y (List.mem_append_right _ (List.mem_cons_of_mem _ hy)) hm
      simp only [LabelledTree.inorder, List.mem_append, List.mem_cons] at found
      rcases found with found | eq | found
      · exact False.elim (apart y (hl.sublist.subset found) hy)
      · exact False.elim (xr (eq ▸ hy))
      · exact found
    simp only [prune, il dl left, ir dr right]
  | @left l r a x hl il =>
    obtain ⟨dl, dr, xl, xr, apart⟩ := node_distinct distinct
    have unmarked : x ∉ marks := fun hm => xl (hl.sublist.subset
      (covers x (List.mem_append_right _ (List.mem_cons_self ..)) hm))
    have empty : prune marks r = .nil := (prune_nil_iff marks r).mpr (by
      intro y hy hm
      exact apart y (hl.sublist.subset
        (covers y (List.mem_append_right _ (List.mem_cons_of_mem _ hy)) hm)) hy)
    have left := il dl (fun y hy hm => covers y (List.mem_append_left _ hy) hm)
    rw [left]
    cases h : prune marks l <;> simp [prune, join, unmarked, empty, h]
  | @right l r b x hr ir =>
    obtain ⟨dl, dr, xl, xr, apart⟩ := node_distinct distinct
    have unmarked : x ∉ marks := fun hm => xr (hr.sublist.subset
      (covers x (List.mem_append_right _ (List.mem_cons_self ..)) hm))
    have empty : prune marks l = .nil := (prune_nil_iff marks l).mpr (by
      intro y hy hm
      exact apart y hy (hr.sublist.subset (covers y (List.mem_append_left _ hy) hm)))
    have right := ir dr (fun y hy hm => covers y (List.mem_append_right _ (List.mem_cons_of_mem _ hy)) hm)
    rw [right]
    simp [prune, join, unmarked, empty]

end RotationBST.FingerHand
