module

public import RotationBST.Structures.FingerHand.Pruning.Definitions.Abstract
public import RotationBST.Structures.FingerHand.Keys

@[expose] public section
namespace RotationBST.FingerHand

theorem prune_label (marks : Finset Nat) (t : Tree) (lo : Nat) :
    prune marks (t.labelFrom lo) = compress marks t lo := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir => simp only [Tree.labelFrom, prune, il, ir, join, compress]; rfl

theorem prune_sublist (marks : Finset Nat) (t : LabelledTree Nat) :
    (prune marks t).inorder.Sublist t.inorder := by
  induction t with
  | nil => exact .refl _
  | node l x r il ir =>
    have both := il.append (List.Sublist.cons_cons x ir)
    have left := il.trans (List.sublist_append_left l.inorder (x :: r.inorder))
    have right := (ir.cons x).trans (List.sublist_append_right l.inorder (x :: r.inorder))
    by_cases hx : x ∈ marks
    · simpa only [prune, join, hx, ↓reduceIte, LabelledTree.inorder] using both
    · cases hl : prune marks l <;> cases hr : prune marks r <;>
        simp only [prune, join, hx, ↓reduceIte, hl, hr, LabelledTree.inorder] at *
      · exact List.nil_sublist _
      · exact right
      · exact left
      · exact both

theorem prune_nil_iff (marks : Finset Nat) (t : LabelledTree Nat) :
    prune marks t = .nil ↔ ∀ x ∈ t.inorder, x ∉ marks := by
  induction t with
  | nil => simp [prune, LabelledTree.inorder]
  | node l x r il ir =>
    by_cases hx : x ∈ marks <;>
      cases hl : prune marks l <;> cases hr : prune marks r <;>
      simp_all [prune, join, LabelledTree.inorder] <;> aesop

theorem prune_congr (a b : Finset Nat) (t : LabelledTree Nat)
    (same : ∀ x ∈ t.inorder, x ∈ a ↔ x ∈ b) : prune a t = prune b t := by
  induction t with
  | nil => rfl
  | node l x r il ir =>
    have hl := il (fun y hy => same y (List.mem_append_left _ hy))
    have hr := ir (fun y hy => same y (List.mem_append_right _ (List.mem_cons_of_mem _ hy)))
    have hx := same x (List.mem_append_right _ (List.mem_cons_self ..))
    simp only [prune, hl, hr, join, hx]

/-- Recompression needs only the old skeleton when the new marks are a subset
of the old marks. Suppressed paths need not be reconstructed. -/
theorem prune_prune {a b : Finset Nat} (sub : a ⊆ b) (t : LabelledTree Nat) :
    prune a (prune b t) = prune a t := by
  induction t with
  | nil => rfl
  | node l x r il ir =>
    have nilLeft : prune b l = .nil → prune a l = .nil := fun h =>
      (prune_nil_iff a l).mpr (fun y hy hm => (prune_nil_iff b l).mp h y hy (sub hm))
    have nilRight : prune b r = .nil → prune a r = .nil := fun h =>
      (prune_nil_iff a r).mpr (fun y hy hm => (prune_nil_iff b r).mp h y hy (sub hm))
    by_cases hx : x ∈ b
    · simp only [prune, join, hx, ↓reduceIte, il, ir]
    · have ha : x ∉ a := fun h => hx (sub h)
      cases hl : prune b l <;> cases hr : prune b r
      · simp [prune, join, hx, ha, hl, hr, nilLeft hl, nilRight hr]
      · simpa only [prune, join, hx, ha, ↓reduceIte, hl, hr, nilLeft hl] using ir
      · cases h : prune a l <;>
          simpa only [prune, join, hx, ha, ↓reduceIte, hl, hr, nilRight hr, h] using il
      · simp only [prune, join, hx, ↓reduceIte, hl, hr] at il ir ⊢
        rw [il, ir]

theorem prune_compress {a b : Finset Nat} (sub : a ⊆ b) (t : Tree) (lo : Nat) :
    prune a (compress b t lo) = compress a t lo := by
  rw [← prune_label, ← prune_label, prune_prune sub]

theorem compress_submarks {a b : Finset Nat} (sub : a ⊆ b) (t : Tree) (lo : Nat) :
    (compress a t lo).inorder.Sublist (compress b t lo).inorder := by
  rw [← prune_compress sub]
  exact prune_sublist a _

end RotationBST.FingerHand
