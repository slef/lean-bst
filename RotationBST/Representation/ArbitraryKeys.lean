module

public import RotationBST.Representation.AbstractBridge

@[expose] public section

namespace RotationBST.Representation.Bridge

variable {α : Type} {a b : Tree} {s t : LabelledTree α} {k : Nat}

/-- Any shape rotation can be performed on any labelling of that shape. -/
theorem lift_rotate (h : Rotate a b) (s : LabelledTree α) (hs : s.erase = a) :
    ∃ t, LabelledTree.Rotate s t ∧ t.erase = b := by
  induction h generalizing s with
  | right =>
      cases s with
      | nil => cases hs
      | node l y c =>
          cases l with
          | nil => cases hs
          | node a x b =>
              cases hs
              exact ⟨.node a x (.node b y c), .right, rfl⟩
  | left =>
      cases s with
      | nil => cases hs
      | node a x r =>
          cases r with
          | nil => cases hs
          | node b y c =>
              cases hs
              exact ⟨.node (.node a x b) y c, .left, rfl⟩
  | inLeft h ih =>
      cases s with
      | nil => cases hs
      | node l x r =>
          obtain ⟨hl, hr⟩ := Tree.node.inj hs
          obtain ⟨t, ht, he⟩ := ih l hl
          exact ⟨.node t x r, .inLeft ht, by simp only [LabelledTree.erase, he, hr]⟩
  | inRight h ih =>
      cases s with
      | nil => cases hs
      | node l x r =>
          obtain ⟨hl, hr⟩ := Tree.node.inj hs
          obtain ⟨t, ht, he⟩ := ih r hr
          exact ⟨.node l x t, .inRight ht, by simp only [LabelledTree.erase, he, hl]⟩

theorem lift_rotations (h : Rotations a b k) (s : LabelledTree α) (hs : s.erase = a) :
    ∃ t, LabelledTree.Rotations s t k ∧ t.erase = b := by
  induction h generalizing s with
  | refl => exact ⟨s, .refl, hs⟩
  | step h _ ih =>
      obtain ⟨u, hu, he⟩ := lift_rotate h s hs
      obtain ⟨t, ht, he⟩ := ih u he
      exact ⟨t, .step hu ht, he⟩

theorem inorder_rotations (h : LabelledTree.Rotations s t k) : s.inorder = t.inorder := by
  induction h with
  | refl => rfl
  | step h _ ih => exact (inorder_rotate h).trans ih

/-- Cost-preserving correspondence for arbitrary keys, not only consecutive integers.
Fixing the inorder sequence fixes which key belongs to each implicit rank. -/
theorem arbitrary_rotations_iff (s t : LabelledTree α) (keys : s.inorder = t.inorder) :
    Rotations s.erase t.erase k ↔ LabelledTree.Rotations s t k := by
  constructor
  · intro h
    obtain ⟨u, hu, he⟩ := lift_rotations h s rfl
    have hu' : u = t := ext u t he ((inorder_rotations hu).symm.trans keys)
    exact hu' ▸ hu
  · exact erase_rotations

/-- Every shape admits a labelling by any key list of the matching length.
For a strictly increasing key list this is the ordinary BST on precisely those keys. -/
theorem labels_exist (t : Tree) (keys : List α) (h : keys.length = t.size) :
    ∃ u : LabelledTree α, u.erase = t ∧ u.inorder = keys := by
  induction t generalizing keys with
  | nil =>
      have hk : keys = [] := List.length_eq_zero_iff.mp h
      exact ⟨.nil, rfl, hk.symm⟩
  | node l r il ir =>
      have hi : l.size < keys.length := by simp only [Tree.size] at h; omega
      have hl : (keys.take l.size).length = l.size := by
        simp only [List.length_take]; omega
      have hr : (keys.drop (l.size + 1)).length = r.size := by
        simp only [List.length_drop, Tree.size] at *; omega
      obtain ⟨a, ha, hka⟩ := il (keys.take l.size) hl
      obtain ⟨b, hb, hkb⟩ := ir (keys.drop (l.size + 1)) hr
      refine ⟨.node a keys[l.size] b, ?_, ?_⟩
      · simp only [LabelledTree.erase, ha, hb]
      · simp only [LabelledTree.inorder, hka, hkb]
        rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]

end RotationBST.Representation.Bridge
